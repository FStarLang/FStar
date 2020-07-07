open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar
type lstring = Prims.string FStar_Thunk.t
let (mklstr : (unit -> Prims.string) -> Prims.string FStar_Thunk.thunk) =
  fun f ->
    let uf = FStar_Syntax_Unionfind.get () in
    FStar_Thunk.mk
      (fun uu____43 ->
         let tx = FStar_Syntax_Unionfind.new_transaction () in
         FStar_Syntax_Unionfind.set uf;
         (let r = f () in FStar_Syntax_Unionfind.rollback tx; r))
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee -> match projectee with | TERM _0 -> true | uu____81 -> false
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | TERM _0 -> _0
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee ->
    match projectee with | UNIV _0 -> true | uu____116 -> false
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
      (fun uu____700 ->
         match uu____700 with
         | (uu____716, m, p) ->
             let uu____727 = FStar_Thunk.force m in (uu____727, p)) wl_def
let (as_wl_deferred :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun wl ->
    fun d ->
      FStar_List.map
        (fun uu____779 ->
           match uu____779 with
           | (m, p) ->
               let uu____799 = FStar_Thunk.mkv m in ((wl.ctr), uu____799, p))
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
                    let uu____892 = FStar_Syntax_Unionfind.fresh r in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____892;
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
                   (let uu____926 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace") in
                    if uu____926
                    then
                      let uu____930 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____930
                    else ());
                   (ctx_uvar, t,
                     ((let uu___94_936 = wl in
                       {
                         attempting = (uu___94_936.attempting);
                         wl_deferred = (uu___94_936.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___94_936.wl_deferred_to_tac);
                         ctr = (uu___94_936.ctr);
                         defer_ok = (uu___94_936.defer_ok);
                         smt_ok = (uu___94_936.smt_ok);
                         umax_heuristic_ok = (uu___94_936.umax_heuristic_ok);
                         tcenv = (uu___94_936.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits));
                         repr_subcomp_allowed =
                           (uu___94_936.repr_subcomp_allowed)
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
            let uu___100_969 = wl.tcenv in
            {
              FStar_TypeChecker_Env.solver =
                (uu___100_969.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___100_969.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___100_969.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___100_969.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___100_969.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___100_969.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___100_969.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___100_969.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___100_969.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___100_969.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___100_969.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___100_969.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___100_969.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___100_969.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___100_969.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___100_969.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___100_969.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___100_969.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___100_969.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___100_969.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___100_969.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___100_969.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___100_969.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___100_969.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___100_969.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___100_969.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___100_969.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___100_969.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___100_969.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___100_969.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___100_969.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___100_969.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___100_969.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___100_969.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___100_969.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___100_969.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___100_969.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___100_969.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___100_969.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___100_969.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___100_969.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___100_969.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___100_969.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___100_969.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___100_969.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___100_969.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let env1 = FStar_TypeChecker_Env.push_binders env bs in
          let uu____971 = FStar_TypeChecker_Env.all_binders env1 in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____971 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee ->
    match projectee with | Success _0 -> true | uu____1022 -> false
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred *
      FStar_TypeChecker_Common.implicits))
  = fun projectee -> match projectee with | Success _0 -> _0
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee ->
    match projectee with | Failed _0 -> true | uu____1063 -> false
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
        let uu___109_1100 = wl in
        let uu____1101 =
          let uu____1111 = as_wl_deferred wl defer_to_tac in
          FStar_List.append wl.wl_deferred_to_tac uu____1111 in
        {
          attempting = (uu___109_1100.attempting);
          wl_deferred = (uu___109_1100.wl_deferred);
          wl_deferred_to_tac = uu____1101;
          ctr = (uu___109_1100.ctr);
          defer_ok = (uu___109_1100.defer_ok);
          smt_ok = (uu___109_1100.smt_ok);
          umax_heuristic_ok = (uu___109_1100.umax_heuristic_ok);
          tcenv = (uu___109_1100.tcenv);
          wl_implicits = (FStar_List.append wl.wl_implicits imps);
          repr_subcomp_allowed = (uu___109_1100.repr_subcomp_allowed)
        }
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | COVARIANT -> true | uu____1137 -> false
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | CONTRAVARIANT -> true | uu____1148 -> false
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | INVARIANT -> true | uu____1159 -> false
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_1177 ->
    match uu___0_1177 with
    | FStar_TypeChecker_Common.EQ -> "="
    | FStar_TypeChecker_Common.SUB -> "<:"
    | FStar_TypeChecker_Common.SUBINV -> ":>"
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    let uu____1189 = FStar_Syntax_Util.head_and_args t in
    match uu____1189 with
    | (head, args) ->
        (match head.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
             let uu____1252 = FStar_Syntax_Print.ctx_uvar_to_string u in
             let uu____1254 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1269 =
                     let uu____1271 = FStar_List.hd s1 in
                     FStar_Syntax_Print.subst_to_string uu____1271 in
                   FStar_Util.format1 "@<%s>" uu____1269 in
             let uu____1275 = FStar_Syntax_Print.args_to_string args in
             FStar_Util.format3 "%s%s %s" uu____1252 uu____1254 uu____1275
         | uu____1278 -> FStar_Syntax_Print.term_to_string t)
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env ->
    fun uu___1_1290 ->
      match uu___1_1290 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1295 =
            let uu____1299 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____1301 =
              let uu____1305 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____1307 =
                let uu____1311 =
                  let uu____1315 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____1315] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1311 in
              uu____1305 :: uu____1307 in
            uu____1299 :: uu____1301 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1295
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1326 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1328 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____1330 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1326 uu____1328
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1330
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env ->
    fun uu___2_1344 ->
      match uu___2_1344 with
      | UNIV (u, t) ->
          let x =
            let uu____1350 = FStar_Options.hide_uvar_nums () in
            if uu____1350
            then "?"
            else
              (let uu____1357 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____1357 FStar_Util.string_of_int) in
          let uu____1361 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s <- %s" x uu____1361
      | TERM (u, t) ->
          let x =
            let uu____1368 = FStar_Options.hide_uvar_nums () in
            if uu____1368
            then "?"
            else
              (let uu____1375 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head in
               FStar_All.pipe_right uu____1375 FStar_Util.string_of_int) in
          let uu____1379 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s <- %s" x uu____1379
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env -> fun uvis -> FStar_Common.string_of_list (uvi_to_string env) uvis
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms ->
    let uu____1409 =
      let uu____1413 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1413
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1409 (FStar_String.concat ", ")
let args_to_string :
  'uuuuuu1432 .
    (FStar_Syntax_Syntax.term * 'uuuuuu1432) Prims.list -> Prims.string
  =
  fun args ->
    let uu____1451 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1472 ->
              match uu____1472 with
              | (x, uu____1479) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1451 (FStar_String.concat " ")
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
        (let uu____1527 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1527
         then
           let uu____1532 = FStar_Thunk.force reason in
           let uu____1535 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1532 uu____1535
         else ());
        Failed (prob, reason)
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env ->
    fun reason ->
      fun prob ->
        let uu____1558 = mklstr (fun uu____1561 -> reason) in
        giveup env uu____1558 prob
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1567 ->
    match uu___3_1567 with
    | FStar_TypeChecker_Common.EQ -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV -> FStar_TypeChecker_Common.SUB
let invert :
  'uuuuuu1573 .
    'uuuuuu1573 FStar_TypeChecker_Common.problem ->
      'uuuuuu1573 FStar_TypeChecker_Common.problem
  =
  fun p ->
    let uu___169_1585 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___169_1585.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___169_1585.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___169_1585.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___169_1585.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___169_1585.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___169_1585.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___169_1585.FStar_TypeChecker_Common.rank)
    }
let maybe_invert :
  'uuuuuu1593 .
    'uuuuuu1593 FStar_TypeChecker_Common.problem ->
      'uuuuuu1593 FStar_TypeChecker_Common.problem
  =
  fun p ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1613 ->
    match uu___4_1613 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1619 -> FStar_TypeChecker_Common.TProb uu____1619)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1625 -> FStar_TypeChecker_Common.CProb uu____1625)
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1631 ->
    match uu___5_1631 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___181_1637 = p in
           {
             FStar_TypeChecker_Common.pid =
               (uu___181_1637.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___181_1637.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___181_1637.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___181_1637.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___181_1637.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___181_1637.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___181_1637.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___181_1637.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___181_1637.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___185_1645 = p in
           {
             FStar_TypeChecker_Common.pid =
               (uu___185_1645.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___185_1645.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___185_1645.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___185_1645.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___185_1645.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___185_1645.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___185_1645.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___185_1645.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___185_1645.FStar_TypeChecker_Common.rank)
           })
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel ->
    fun uu___6_1658 ->
      match uu___6_1658 with
      | INVARIANT -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT -> invert_rel rel
      | COVARIANT -> rel
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1665 ->
    match uu___7_1665 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1678 ->
    match uu___8_1678 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1693 ->
    match uu___9_1693 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1708 ->
    match uu___10_1708 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1722 ->
    match uu___11_1722 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1736 ->
    match uu___12_1736 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1748 ->
    match uu___13_1748 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
let def_scope_wf :
  'uuuuuu1764 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu1764) Prims.list -> unit
  =
  fun msg ->
    fun rng ->
      fun r ->
        let uu____1794 =
          let uu____1796 = FStar_Options.defensive () in
          Prims.op_Negation uu____1796 in
        if uu____1794
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv, uu____1833)::bs ->
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
          let uu____1880 =
            match p_element prob with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1904 = FStar_Syntax_Syntax.mk_binder x in
                [uu____1904] in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1880
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1932 =
            match p_element prob with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1956 = FStar_Syntax_Syntax.mk_binder x in
                [uu____1956] in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1932 in
    def_scope_wf "p_scope" (p_loc prob) r; r
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg ->
    fun prob ->
      fun phi ->
        let uu____2003 =
          let uu____2005 = FStar_Options.defensive () in
          Prims.op_Negation uu____2005 in
        if uu____2003
        then ()
        else
          (let uu____2010 =
             let uu____2013 = p_scope prob in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____2013 in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____2010 phi)
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg ->
    fun prob ->
      fun comp ->
        let uu____2062 =
          let uu____2064 = FStar_Options.defensive () in
          Prims.op_Negation uu____2064 in
        if uu____2062
        then ()
        else
          (let uu____2069 = FStar_Syntax_Util.arrow [] comp in
           def_check_scoped msg prob uu____2069)
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg ->
    fun prob ->
      let uu____2089 =
        let uu____2091 = FStar_Options.defensive () in
        Prims.op_Negation uu____2091 in
      if uu____2089
      then ()
      else
        (let msgf m =
           let uu____2105 =
             let uu____2107 =
               let uu____2109 = FStar_Util.string_of_int (p_pid prob) in
               Prims.op_Hat uu____2109 (Prims.op_Hat "." m) in
             Prims.op_Hat "." uu____2107 in
           Prims.op_Hat msg uu____2105 in
         (let uu____2114 = msgf "scope" in
          let uu____2117 = p_scope prob in
          def_scope_wf uu____2114 (p_loc prob) uu____2117);
         (let uu____2129 = msgf "guard" in
          def_check_scoped uu____2129 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____2136 = msgf "lhs" in
                def_check_scoped uu____2136 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2139 = msgf "rhs" in
                def_check_scoped uu____2139 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____2146 = msgf "lhs" in
                def_check_scoped_comp uu____2146 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2149 = msgf "rhs" in
                def_check_scoped_comp uu____2149 prob
                  p.FStar_TypeChecker_Common.rhs))))
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl ->
    fun prob ->
      fun smt_ok ->
        let uu___278_2170 = wl in
        {
          attempting = [prob];
          wl_deferred = (uu___278_2170.wl_deferred);
          wl_deferred_to_tac = (uu___278_2170.wl_deferred_to_tac);
          ctr = (uu___278_2170.ctr);
          defer_ok = (uu___278_2170.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___278_2170.umax_heuristic_ok);
          tcenv = (uu___278_2170.tcenv);
          wl_implicits = (uu___278_2170.wl_implicits);
          repr_subcomp_allowed = (uu___278_2170.repr_subcomp_allowed)
        }
let wl_of_guard :
  'uuuuuu2178 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu2178 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env ->
    fun g ->
      let uu___282_2201 = empty_worklist env in
      let uu____2202 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____2202;
        wl_deferred = (uu___282_2201.wl_deferred);
        wl_deferred_to_tac = (uu___282_2201.wl_deferred_to_tac);
        ctr = (uu___282_2201.ctr);
        defer_ok = (uu___282_2201.defer_ok);
        smt_ok = (uu___282_2201.smt_ok);
        umax_heuristic_ok = (uu___282_2201.umax_heuristic_ok);
        tcenv = (uu___282_2201.tcenv);
        wl_implicits = (uu___282_2201.wl_implicits);
        repr_subcomp_allowed = (uu___282_2201.repr_subcomp_allowed)
      }
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason ->
    fun prob ->
      fun wl ->
        let uu___287_2223 = wl in
        {
          attempting = (uu___287_2223.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          wl_deferred_to_tac = (uu___287_2223.wl_deferred_to_tac);
          ctr = (uu___287_2223.ctr);
          defer_ok = (uu___287_2223.defer_ok);
          smt_ok = (uu___287_2223.smt_ok);
          umax_heuristic_ok = (uu___287_2223.umax_heuristic_ok);
          tcenv = (uu___287_2223.tcenv);
          wl_implicits = (uu___287_2223.wl_implicits);
          repr_subcomp_allowed = (uu___287_2223.repr_subcomp_allowed)
        }
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason ->
    fun prob ->
      fun wl ->
        let uu____2250 = FStar_Thunk.mkv reason in defer uu____2250 prob wl
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs ->
    fun wl ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___295_2269 = wl in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___295_2269.wl_deferred);
         wl_deferred_to_tac = (uu___295_2269.wl_deferred_to_tac);
         ctr = (uu___295_2269.ctr);
         defer_ok = (uu___295_2269.defer_ok);
         smt_ok = (uu___295_2269.smt_ok);
         umax_heuristic_ok = (uu___295_2269.umax_heuristic_ok);
         tcenv = (uu___295_2269.tcenv);
         wl_implicits = (uu___295_2269.wl_implicits);
         repr_subcomp_allowed = (uu___295_2269.repr_subcomp_allowed)
       })
let mk_eq2 :
  'uuuuuu2283 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2283 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl ->
    fun env ->
      fun prob ->
        fun t1 ->
          fun t2 ->
            let uu____2317 = FStar_Syntax_Util.type_u () in
            match uu____2317 with
            | (t_type, u) ->
                let binders = FStar_TypeChecker_Env.all_binders env in
                let uu____2329 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None in
                (match uu____2329 with
                 | (uu____2341, tt, wl1) ->
                     let uu____2344 = FStar_Syntax_Util.mk_eq2 u tt t1 t2 in
                     (uu____2344, wl1))
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2350 ->
    match uu___14_2350 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun uu____2356 -> FStar_TypeChecker_Common.TProb uu____2356)
          (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun uu____2362 -> FStar_TypeChecker_Common.CProb uu____2362)
          (invert p)
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p ->
    let uu____2370 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____2370 = Prims.int_one
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero in
  fun uu____2390 -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem :
  'uuuuuu2432 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'uuuuuu2432 ->
            FStar_TypeChecker_Common.rel ->
              'uuuuuu2432 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuuu2432 FStar_TypeChecker_Common.problem * worklist)
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
                        let uu____2519 =
                          let uu____2528 = FStar_Syntax_Syntax.mk_binder x in
                          [uu____2528] in
                        FStar_List.append scope uu____2519 in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1 in
                  let gamma =
                    let uu____2571 =
                      let uu____2574 =
                        FStar_List.map
                          (fun b ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1 in
                      FStar_List.rev uu____2574 in
                    FStar_List.append uu____2571
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma in
                  let uu____2593 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None in
                  match uu____2593 with
                  | (ctx_uvar, lg, wl1) ->
                      let prob =
                        let uu____2613 = next_pid () in
                        {
                          FStar_TypeChecker_Common.pid = uu____2613;
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
                  (let uu____2687 =
                     mk_problem wl scope orig lhs rel rhs elt reason in
                   match uu____2687 with
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
                  (let uu____2775 =
                     mk_problem wl scope orig lhs rel rhs elt reason in
                   match uu____2775 with
                   | (p, wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
let new_problem :
  'uuuuuu2813 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2813 ->
          FStar_TypeChecker_Common.rel ->
            'uuuuuu2813 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('uuuuuu2813 FStar_TypeChecker_Common.problem * worklist)
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
                          let uu____2881 = FStar_Syntax_Syntax.mk_binder x in
                          [uu____2881] in
                        let uu____2900 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        FStar_Syntax_Util.arrow bs uu____2900 in
                  let uu____2903 =
                    let uu____2910 = FStar_TypeChecker_Env.all_binders env in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___378_2921 = wl in
                       {
                         attempting = (uu___378_2921.attempting);
                         wl_deferred = (uu___378_2921.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___378_2921.wl_deferred_to_tac);
                         ctr = (uu___378_2921.ctr);
                         defer_ok = (uu___378_2921.defer_ok);
                         smt_ok = (uu___378_2921.smt_ok);
                         umax_heuristic_ok =
                           (uu___378_2921.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___378_2921.wl_implicits);
                         repr_subcomp_allowed =
                           (uu___378_2921.repr_subcomp_allowed)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2910
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None in
                  match uu____2903 with
                  | (ctx_uvar, lg, wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____2933 =
                              let uu____2934 =
                                let uu____2943 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.as_arg uu____2943 in
                              [uu____2934] in
                            FStar_Syntax_Syntax.mk_Tm_app lg uu____2933 loc in
                      let prob =
                        let uu____2971 = next_pid () in
                        {
                          FStar_TypeChecker_Common.pid = uu____2971;
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
                let uu____3019 = next_pid () in
                {
                  FStar_TypeChecker_Common.pid = uu____3019;
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
  'uuuuuu3034 .
    worklist ->
      'uuuuuu3034 FStar_TypeChecker_Common.problem ->
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
              let uu____3067 =
                let uu____3070 =
                  let uu____3071 =
                    let uu____3078 = FStar_Syntax_Syntax.bv_to_name e in
                    (x, uu____3078) in
                  FStar_Syntax_Syntax.NT uu____3071 in
                [uu____3070] in
              FStar_Syntax_Subst.subst uu____3067 phi
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env ->
    fun d ->
      fun s ->
        let uu____3100 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")) in
        if uu____3100
        then
          let uu____3108 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____3111 = prob_to_string env d in
          let uu____3113 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          let uu____3120 = FStar_Thunk.force s in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3108 uu____3111 uu____3113 uu____3120
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ -> "equal to"
             | FStar_TypeChecker_Common.SUB -> "a subtype of"
             | uu____3132 -> failwith "impossible" in
           let uu____3135 =
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
           match uu____3135 with
           | (lhs, rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let (commit : uvi Prims.list -> unit) =
  fun uvis ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3178 ->
            match uu___15_3178 with
            | UNIV (u, t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3192 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u, t) ->
                ((let uu____3196 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3196 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___16_3227 ->
           match uu___16_3227 with
           | UNIV uu____3230 -> FStar_Pervasives_Native.None
           | TERM (u, t) ->
               let uu____3237 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head in
               if uu____3237
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
        (fun uu___17_3265 ->
           match uu___17_3265 with
           | UNIV (u', t) ->
               let uu____3270 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____3270
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3277 -> FStar_Pervasives_Native.None)
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____3289 =
        let uu____3290 =
          let uu____3291 = FStar_Syntax_Util.unmeta t in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3291 in
        FStar_Syntax_Subst.compress uu____3290 in
      FStar_All.pipe_right uu____3289 FStar_Syntax_Util.unlazy_emb
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____3303 =
        let uu____3304 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t in
        FStar_Syntax_Subst.compress uu____3304 in
      FStar_All.pipe_right uu____3303 FStar_Syntax_Util.unlazy_emb
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____3316 =
        let uu____3320 =
          let uu____3322 = FStar_TypeChecker_Env.current_module env in
          FStar_Ident.string_of_lid uu____3322 in
        FStar_Pervasives_Native.Some uu____3320 in
      FStar_Profiling.profile (fun uu____3325 -> sn' env t) uu____3316
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
          let uu____3350 =
            let uu____3354 =
              let uu____3356 = FStar_TypeChecker_Env.current_module env in
              FStar_Ident.string_of_lid uu____3356 in
            FStar_Pervasives_Native.Some uu____3354 in
          FStar_Profiling.profile
            (fun uu____3359 ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3350
            profiling_tag
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____3367 = FStar_Syntax_Util.head_and_args t in
    match uu____3367 with
    | (h, uu____3386) ->
        let uu____3411 =
          let uu____3412 = FStar_Syntax_Subst.compress h in
          uu____3412.FStar_Syntax_Syntax.n in
        (match uu____3411 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> true
         | uu____3417 -> false)
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____3430 =
        let uu____3434 =
          let uu____3436 = FStar_TypeChecker_Env.current_module env in
          FStar_Ident.string_of_lid uu____3436 in
        FStar_Pervasives_Native.Some uu____3434 in
      FStar_Profiling.profile
        (fun uu____3441 ->
           let uu____3442 = should_strongly_reduce t in
           if uu____3442
           then
             let uu____3445 =
               let uu____3446 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t in
               FStar_Syntax_Subst.compress uu____3446 in
             FStar_All.pipe_right uu____3445 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3430 "FStar.TypeChecker.Rel.whnf"
let norm_arg :
  'uuuuuu3457 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu3457) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu3457)
  =
  fun env ->
    fun t ->
      let uu____3480 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____3480, (FStar_Pervasives_Native.snd t))
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
           (fun uu____3532 ->
              match uu____3532 with
              | (x, imp) ->
                  let uu____3551 =
                    let uu___484_3552 = x in
                    let uu____3553 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___484_3552.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___484_3552.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3553
                    } in
                  (uu____3551, imp)))
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3577 = aux u3 in FStar_Syntax_Syntax.U_succ uu____3577
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3581 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____3581
        | uu____3584 -> u2 in
      let uu____3585 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3585
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun t0 ->
        let uu____3602 =
          let uu____3606 =
            let uu____3608 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____3608 in
          FStar_Pervasives_Native.Some uu____3606 in
        FStar_Profiling.profile
          (fun uu____3611 ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3602 "FStar.TypeChecker.Rel.normalize_refinement"
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
                (let uu____3733 = norm_refinement env t12 in
                 match uu____3733 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1, phi1);
                     FStar_Syntax_Syntax.pos = uu____3748;
                     FStar_Syntax_Syntax.vars = uu____3749;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3773 =
                       let uu____3775 = FStar_Syntax_Print.term_to_string tt in
                       let uu____3777 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3775 uu____3777 in
                     failwith uu____3773)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3793 = FStar_Syntax_Util.unfold_lazy i in
              aux norm uu____3793
          | FStar_Syntax_Syntax.Tm_uinst uu____3794 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____3831 =
                   let uu____3832 = FStar_Syntax_Subst.compress t1' in
                   uu____3832.FStar_Syntax_Syntax.n in
                 match uu____3831 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3847 -> aux true t1'
                 | uu____3855 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3870 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____3901 =
                   let uu____3902 = FStar_Syntax_Subst.compress t1' in
                   uu____3902.FStar_Syntax_Syntax.n in
                 match uu____3901 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3917 -> aux true t1'
                 | uu____3925 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____3940 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____3987 =
                   let uu____3988 = FStar_Syntax_Subst.compress t1' in
                   uu____3988.FStar_Syntax_Syntax.n in
                 match uu____3987 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4003 -> aux true t1'
                 | uu____4011 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____4026 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____4041 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____4056 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____4071 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____4086 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____4115 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____4148 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____4169 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____4196 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____4224 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____4261 ->
              let uu____4268 =
                let uu____4270 = FStar_Syntax_Print.term_to_string t12 in
                let uu____4272 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4270 uu____4272 in
              failwith uu____4268
          | FStar_Syntax_Syntax.Tm_ascribed uu____4287 ->
              let uu____4314 =
                let uu____4316 = FStar_Syntax_Print.term_to_string t12 in
                let uu____4318 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4316 uu____4318 in
              failwith uu____4314
          | FStar_Syntax_Syntax.Tm_delayed uu____4333 ->
              let uu____4348 =
                let uu____4350 = FStar_Syntax_Print.term_to_string t12 in
                let uu____4352 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4350 uu____4352 in
              failwith uu____4348
          | FStar_Syntax_Syntax.Tm_unknown ->
              let uu____4367 =
                let uu____4369 = FStar_Syntax_Print.term_to_string t12 in
                let uu____4371 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4369 uu____4371 in
              failwith uu____4367 in
        let uu____4386 = whnf env t1 in aux false uu____4386
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
      let uu____4431 = base_and_refinement env t in
      FStar_All.pipe_right uu____4431 FStar_Pervasives_Native.fst
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t ->
    let uu____4472 = FStar_Syntax_Syntax.null_bv t in
    (uu____4472, FStar_Syntax_Util.t_true)
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta ->
    fun env ->
      fun t ->
        let uu____4499 = base_and_refinement_maybe_delta delta env t in
        match uu____4499 with
        | (t_base, refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x, phi) -> (x, phi))
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4559 ->
    match uu____4559 with
    | (t_base, refopt) ->
        let uu____4590 =
          match refopt with
          | FStar_Pervasives_Native.Some (y, phi) -> (y, phi)
          | FStar_Pervasives_Native.None -> trivial_refinement t_base in
        (match uu____4590 with
         | (y, phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               t_base.FStar_Syntax_Syntax.pos)
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl -> fun prob -> prob_to_string wl.tcenv prob
let (wl_to_string : worklist -> Prims.string) =
  fun wl ->
    let uu____4632 =
      let uu____4636 =
        let uu____4639 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4664 ->
                  match uu____4664 with | (uu____4672, uu____4673, x) -> x)) in
        FStar_List.append wl.attempting uu____4639 in
      FStar_List.map (wl_prob_to_string wl) uu____4636 in
    FStar_All.pipe_right uu____4632 (FStar_String.concat "\n\t")
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
  fun uu____4733 ->
    match uu____4733 with
    | Flex (uu____4735, u, uu____4737) ->
        u.FStar_Syntax_Syntax.ctx_uvar_reason
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4744 ->
    match uu____4744 with
    | Flex (uu____4746, c, args) ->
        let uu____4749 = print_ctx_uvar c in
        let uu____4751 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "%s [%s]" uu____4749 uu____4751
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____4761 = FStar_Syntax_Util.head_and_args t in
    match uu____4761 with
    | (head, _args) ->
        let uu____4805 =
          let uu____4806 = FStar_Syntax_Subst.compress head in
          uu____4806.FStar_Syntax_Syntax.n in
        (match uu____4805 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4810 -> true
         | uu____4824 -> false)
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t ->
    let uu____4832 = FStar_Syntax_Util.head_and_args t in
    match uu____4832 with
    | (head, _args) ->
        let uu____4875 =
          let uu____4876 = FStar_Syntax_Subst.compress head in
          uu____4876.FStar_Syntax_Syntax.n in
        (match uu____4875 with
         | FStar_Syntax_Syntax.Tm_uvar (u, uu____4880) -> u
         | uu____4897 -> failwith "Not a flex-uvar")
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0 ->
    fun wl ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x in
        let t_x' = FStar_Syntax_Subst.subst' s t_x in
        let uu____4933 =
          let uu____4934 = FStar_Syntax_Subst.compress t_x' in
          uu____4934.FStar_Syntax_Syntax.n in
        match uu____4933 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____4939 -> false in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____4955 -> true in
      let uu____4957 = FStar_Syntax_Util.head_and_args t0 in
      match uu____4957 with
      | (head, args) ->
          let uu____5004 =
            let uu____5005 = FStar_Syntax_Subst.compress head in
            uu____5005.FStar_Syntax_Syntax.n in
          (match uu____5004 with
           | FStar_Syntax_Syntax.Tm_uvar (uv, ([], uu____5013)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv, uu____5029) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
               let uu____5070 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma in
               (match uu____5070 with
                | (gamma_aff, new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____5097 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff in
                         let uu____5101 =
                           let uu____5108 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma in
                           let uu____5117 =
                             let uu____5120 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                             FStar_Syntax_Util.arrow dom_binders uu____5120 in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____5108
                             uu____5117
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta in
                         (match uu____5101 with
                          | (v, t_v, wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____5156 ->
                                     match uu____5156 with
                                     | (x, i) ->
                                         let uu____5175 =
                                           FStar_Syntax_Syntax.bv_to_name x in
                                         (uu____5175, i)) dom_binders in
                              let sol =
                                FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                  t0.FStar_Syntax_Syntax.pos in
                              (FStar_Syntax_Util.set_uvar
                                 uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                               (let args_sol_s =
                                  FStar_List.map
                                    (fun uu____5205 ->
                                       match uu____5205 with
                                       | (a, i) ->
                                           let uu____5224 =
                                             FStar_Syntax_Subst.subst' s a in
                                           (uu____5224, i)) args_sol in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    t0.FStar_Syntax_Syntax.pos in
                                (t, wl1))))))
           | uu____5234 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t ->
    let uu____5246 = FStar_Syntax_Util.head_and_args t in
    match uu____5246 with
    | (head, args) ->
        let uu____5289 =
          let uu____5290 = FStar_Syntax_Subst.compress head in
          uu____5290.FStar_Syntax_Syntax.n in
        (match uu____5289 with
         | FStar_Syntax_Syntax.Tm_uvar (uv, s) -> Flex (t, uv, args)
         | uu____5311 -> failwith "Not a flex-uvar")
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t ->
    fun wl ->
      let uu____5332 = ensure_no_uvar_subst t wl in
      match uu____5332 with
      | (t1, wl1) ->
          let uu____5343 = destruct_flex_t' t1 in (uu____5343, wl1)
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k ->
    fun ys ->
      fun t ->
        let uu____5360 =
          let uu____5383 =
            let uu____5384 = FStar_Syntax_Subst.compress k in
            uu____5384.FStar_Syntax_Syntax.n in
          match uu____5383 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5466 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____5466)
              else
                (let uu____5501 = FStar_Syntax_Util.abs_formals t in
                 match uu____5501 with
                 | (ys', t1, uu____5534) ->
                     let uu____5539 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____5539))
          | uu____5578 ->
              let uu____5579 =
                let uu____5584 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____5584) in
              ((ys, t), uu____5579) in
        match uu____5360 with
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
                 let uu____5679 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____5679 c in
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
               (let uu____5757 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel") in
                if uu____5757
                then
                  let uu____5762 = FStar_Util.string_of_int (p_pid prob) in
                  let uu____5764 = print_ctx_uvar uv in
                  let uu____5766 = FStar_Syntax_Print.term_to_string phi1 in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5762 uu____5764 uu____5766
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0)) in
                (let uu____5775 =
                   let uu____5777 = FStar_Util.string_of_int (p_pid prob) in
                   Prims.op_Hat "solve_prob'.sol." uu____5777 in
                 let uu____5780 =
                   let uu____5783 = p_scope prob in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5783 in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5775 uu____5780 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2) in
             let uv = p_guard_uvar prob in
             let fail uu____5816 =
               let uu____5817 =
                 let uu____5819 = FStar_Syntax_Print.ctx_uvar_to_string uv in
                 let uu____5821 =
                   FStar_Syntax_Print.term_to_string (p_guard prob) in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5819 uu____5821 in
               failwith uu____5817 in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5887 ->
                       match uu____5887 with
                       | (a, i) ->
                           let uu____5908 =
                             let uu____5909 = FStar_Syntax_Subst.compress a in
                             uu____5909.FStar_Syntax_Syntax.n in
                           (match uu____5908 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5935 -> (fail (); [])))) in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob) in
               let uu____5945 =
                 let uu____5947 = is_flex g in Prims.op_Negation uu____5947 in
               if uu____5945
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____5956 = destruct_flex_t g wl in
                  match uu____5956 with
                  | (Flex (uu____5961, uv1, args), wl1) ->
                      ((let uu____5966 = args_as_binders args in
                        assign_solution uu____5966 uv1 phi);
                       wl1)) in
             commit uvis;
             (let uu___762_5968 = wl1 in
              {
                attempting = (uu___762_5968.attempting);
                wl_deferred = (uu___762_5968.wl_deferred);
                wl_deferred_to_tac = (uu___762_5968.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___762_5968.defer_ok);
                smt_ok = (uu___762_5968.smt_ok);
                umax_heuristic_ok = (uu___762_5968.umax_heuristic_ok);
                tcenv = (uu___762_5968.tcenv);
                wl_implicits = (uu___762_5968.wl_implicits);
                repr_subcomp_allowed = (uu___762_5968.repr_subcomp_allowed)
              }))
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid ->
    fun sol ->
      fun wl ->
        (let uu____5993 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel") in
         if uu____5993
         then
           let uu____5998 = FStar_Util.string_of_int pid in
           let uu____6000 = uvis_to_string wl.tcenv sol in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____5998 uu____6000
         else ());
        commit sol;
        (let uu___770_6006 = wl in
         {
           attempting = (uu___770_6006.attempting);
           wl_deferred = (uu___770_6006.wl_deferred);
           wl_deferred_to_tac = (uu___770_6006.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___770_6006.defer_ok);
           smt_ok = (uu___770_6006.smt_ok);
           umax_heuristic_ok = (uu___770_6006.umax_heuristic_ok);
           tcenv = (uu___770_6006.tcenv);
           wl_implicits = (uu___770_6006.wl_implicits);
           repr_subcomp_allowed = (uu___770_6006.repr_subcomp_allowed)
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
          (let uu____6042 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel") in
           if uu____6042
           then
             let uu____6047 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____6051 = uvis_to_string wl.tcenv uvis in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6047 uu____6051
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
        let uu____6078 = FStar_Syntax_Free.uvars t in
        FStar_All.pipe_right uu____6078 FStar_Util.set_elements in
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
      let uu____6118 = occurs uk t in
      match uu____6118 with
      | (uvars, occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6157 =
                 let uu____6159 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head in
                 let uu____6161 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6159 uu____6161 in
               FStar_Pervasives_Native.Some uu____6157) in
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
          let uu____6272 = FStar_Syntax_Syntax.bv_eq b b' in
          if uu____6272
          then
            let uu____6283 = maximal_prefix bs_tail bs'_tail in
            (match uu____6283 with | (pfx, rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6334 -> ([], (bs, bs'))
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      FStar_List.fold_left
        (fun g1 ->
           fun uu____6391 ->
             match uu____6391 with
             | (x, uu____6403) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      let uu____6421 = FStar_List.last bs in
      match uu____6421 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some (x, uu____6445) ->
          let uu____6456 =
            FStar_Util.prefix_until
              (fun uu___18_6471 ->
                 match uu___18_6471 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6474 -> false) g in
          (match uu____6456 with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some (uu____6488, bx, rest) -> bx ::
               rest)
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt ->
    fun src ->
      fun wl ->
        let uu____6525 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders in
        match uu____6525 with
        | (pfx, uu____6535) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx in
            let uu____6547 =
              let uu____6554 =
                let uu____6556 =
                  FStar_Syntax_Print.uvar_to_string
                    src.FStar_Syntax_Syntax.ctx_uvar_head in
                Prims.op_Hat "restricted " uu____6556 in
              new_uvar uu____6554 wl src.FStar_Syntax_Syntax.ctx_uvar_range g
                pfx src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta in
            (match uu____6547 with
             | (uu____6559, src', wl1) ->
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
                 | uu____6673 -> out) FStar_Syntax_Syntax.no_names g in
        let uu____6674 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6738 ->
                  fun uu____6739 ->
                    match (uu____6738, uu____6739) with
                    | ((isect, isect_set), (x, imp)) ->
                        let uu____6842 =
                          let uu____6844 = FStar_Util.set_mem x v1_set in
                          FStar_All.pipe_left Prims.op_Negation uu____6844 in
                        if uu____6842
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort in
                           let uu____6878 =
                             FStar_Util.set_is_subset_of fvs isect_set in
                           if uu____6878
                           then
                             let uu____6895 = FStar_Util.set_add x isect_set in
                             (((x, imp) :: isect), uu____6895)
                           else (isect, isect_set))) ([], ctx_binders)) in
        match uu____6674 with | (isect, uu____6945) -> FStar_List.rev isect
let binders_eq :
  'uuuuuu6981 'uuuuuu6982 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu6981) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu6982) Prims.list -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7040 ->
              fun uu____7041 ->
                match (uu____7040, uu____7041) with
                | ((a, uu____7060), (b, uu____7062)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let name_exists_in_binders :
  'uuuuuu7078 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7078) Prims.list -> Prims.bool
  =
  fun x ->
    fun bs ->
      FStar_Util.for_some
        (fun uu____7109 ->
           match uu____7109 with
           | (y, uu____7116) -> FStar_Syntax_Syntax.bv_eq x y) bs
let pat_vars :
  'uuuuuu7126 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7126) Prims.list ->
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
                   let uu____7288 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx) in
                   if uu____7288
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7321 -> FStar_Pervasives_Native.None) in
        aux [] args
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu____7373 -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | HeadMatch _0 -> true | uu____7417 -> false
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee -> match projectee with | HeadMatch _0 -> _0
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | FullMatch -> true | uu____7438 -> false
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7446 ->
    match uu___19_7446 with
    | MisMatch (d1, d2) ->
        let uu____7458 =
          let uu____7460 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1 in
          let uu____7462 =
            let uu____7464 =
              let uu____7466 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2 in
              Prims.op_Hat uu____7466 ")" in
            Prims.op_Hat ") (" uu____7464 in
          Prims.op_Hat uu____7460 uu____7462 in
        Prims.op_Hat "MisMatch (" uu____7458
    | HeadMatch u ->
        let uu____7473 = FStar_Util.string_of_bool u in
        Prims.op_Hat "HeadMatch " uu____7473
    | FullMatch -> "FullMatch"
let (head_match : match_result -> match_result) =
  fun uu___20_7482 ->
    match uu___20_7482 with
    | MisMatch (i, j) -> MisMatch (i, j)
    | HeadMatch (true) -> HeadMatch true
    | uu____7499 -> HeadMatch false
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env ->
    fun fv ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7514 =
            (let uu____7520 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule in
             let uu____7522 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             uu____7520 = uu____7522) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) in
          if uu____7514 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7531 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____7531 with
           | FStar_Pervasives_Native.None ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7542 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7566 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7576 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7595 = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env uu____7595
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7596 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7597 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7598 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7611 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7625 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____7649) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____7655, uu____7656) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2, uu____7698) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7723;
             FStar_Syntax_Syntax.index = uu____7724;
             FStar_Syntax_Syntax.sort = t2;_},
           uu____7726)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7734 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7735 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7736 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7751 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7758 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7778 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____7778
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
           { FStar_Syntax_Syntax.blob = uu____7797;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7798;
             FStar_Syntax_Syntax.ltyp = uu____7799;
             FStar_Syntax_Syntax.rng = uu____7800;_},
           uu____7801) ->
            let uu____7812 = FStar_Syntax_Util.unlazy t11 in
            head_matches env uu____7812 t21
        | (uu____7813, FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7814;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7815;
             FStar_Syntax_Syntax.ltyp = uu____7816;
             FStar_Syntax_Syntax.rng = uu____7817;_})
            ->
            let uu____7828 = FStar_Syntax_Util.unlazy t21 in
            head_matches env t11 uu____7828
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7831 = FStar_Syntax_Syntax.bv_eq x y in
            if uu____7831
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7842 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____7842
            then FullMatch
            else
              (let uu____7847 =
                 let uu____7856 =
                   let uu____7859 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____7859 in
                 let uu____7860 =
                   let uu____7863 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____7863 in
                 (uu____7856, uu____7860) in
               MisMatch uu____7847)
        | (FStar_Syntax_Syntax.Tm_uinst (f, uu____7869),
           FStar_Syntax_Syntax.Tm_uinst (g, uu____7871)) ->
            let uu____7880 = head_matches env f g in
            FStar_All.pipe_right uu____7880 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           uu____7881) -> HeadMatch true
        | (uu____7883, FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify)) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7887 = FStar_Const.eq_const c d in
            if uu____7887
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar (uv, uu____7897),
           FStar_Syntax_Syntax.Tm_uvar (uv', uu____7899)) ->
            let uu____7932 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head in
            if uu____7932
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7942),
           FStar_Syntax_Syntax.Tm_refine (y, uu____7944)) ->
            let uu____7953 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7953 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____7955), uu____7956) ->
            let uu____7961 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____7961 head_match
        | (uu____7962, FStar_Syntax_Syntax.Tm_refine (x, uu____7964)) ->
            let uu____7969 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____7969 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____7970,
           FStar_Syntax_Syntax.Tm_type uu____7971) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow uu____7973,
           FStar_Syntax_Syntax.Tm_arrow uu____7974) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app (head, uu____8005),
           FStar_Syntax_Syntax.Tm_app (head', uu____8007)) ->
            let uu____8056 = head_matches env head head' in
            FStar_All.pipe_right uu____8056 head_match
        | (FStar_Syntax_Syntax.Tm_app (head, uu____8058), uu____8059) ->
            let uu____8084 = head_matches env head t21 in
            FStar_All.pipe_right uu____8084 head_match
        | (uu____8085, FStar_Syntax_Syntax.Tm_app (head, uu____8087)) ->
            let uu____8112 = head_matches env t11 head in
            FStar_All.pipe_right uu____8112 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8113, FStar_Syntax_Syntax.Tm_let
           uu____8114) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match uu____8142,
           FStar_Syntax_Syntax.Tm_match uu____8143) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8189, FStar_Syntax_Syntax.Tm_abs
           uu____8190) -> HeadMatch true
        | uu____8228 ->
            let uu____8233 =
              let uu____8242 = delta_depth_of_term env t11 in
              let uu____8245 = delta_depth_of_term env t21 in
              (uu____8242, uu____8245) in
            MisMatch uu____8233
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
              let uu____8314 = unrefine env t in
              FStar_Syntax_Util.head_of uu____8314 in
            (let uu____8316 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____8316
             then
               let uu____8321 = FStar_Syntax_Print.term_to_string t in
               let uu____8323 = FStar_Syntax_Print.term_to_string head in
               FStar_Util.print2 "Head of %s is %s\n" uu____8321 uu____8323
             else ());
            (let uu____8328 =
               let uu____8329 = FStar_Syntax_Util.un_uinst head in
               uu____8329.FStar_Syntax_Syntax.n in
             match uu____8328 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8335 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 (match uu____8335 with
                  | FStar_Pervasives_Native.None ->
                      ((let uu____8349 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta") in
                        if uu____8349
                        then
                          let uu____8354 =
                            FStar_Syntax_Print.term_to_string head in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8354
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8359 ->
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
                      let uu____8377 =
                        let uu____8379 = FStar_Syntax_Util.eq_tm t t' in
                        uu____8379 = FStar_Syntax_Util.Equal in
                      if uu____8377
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8386 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta") in
                          if uu____8386
                          then
                            let uu____8391 =
                              FStar_Syntax_Print.term_to_string t in
                            let uu____8393 =
                              FStar_Syntax_Print.term_to_string t' in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8391
                              uu____8393
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8398 -> FStar_Pervasives_Native.None) in
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
            (let uu____8550 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____8550
             then
               let uu____8555 = FStar_Syntax_Print.term_to_string t11 in
               let uu____8557 = FStar_Syntax_Print.term_to_string t21 in
               let uu____8559 = string_of_match_result r in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8555
                 uu____8557 uu____8559
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
               let uu____8587 =
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
               match uu____8587 with
               | (t12, t22) -> aux retry (n_delta + Prims.int_one) t12 t22 in
             let reduce_both_and_try_again d r1 =
               let uu____8635 = FStar_TypeChecker_Common.decr_delta_depth d in
               match uu____8635 with
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
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8673),
                  uu____8674)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8695 =
                      let uu____8704 = maybe_inline t11 in
                      let uu____8707 = maybe_inline t21 in
                      (uu____8704, uu____8707) in
                    match uu____8695 with
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
                 (uu____8750, FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8751))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8772 =
                      let uu____8781 = maybe_inline t11 in
                      let uu____8784 = maybe_inline t21 in
                      (uu____8781, uu____8784) in
                    match uu____8772 with
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
             | MisMatch uu____8839 -> fail n_delta r t11 t21
             | uu____8848 -> success n_delta r t11 t21) in
          let r = aux true Prims.int_zero t1 t2 in
          (let uu____8863 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta") in
           if uu____8863
           then
             let uu____8868 = FStar_Syntax_Print.term_to_string t1 in
             let uu____8870 = FStar_Syntax_Print.term_to_string t2 in
             let uu____8872 =
               string_of_match_result (FStar_Pervasives_Native.fst r) in
             let uu____8880 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8897 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must in
                  FStar_All.pipe_right uu____8897
                    (fun uu____8932 ->
                       match uu____8932 with
                       | (t11, t21) ->
                           let uu____8940 =
                             FStar_Syntax_Print.term_to_string t11 in
                           let uu____8942 =
                             let uu____8944 =
                               FStar_Syntax_Print.term_to_string t21 in
                             Prims.op_Hat "; " uu____8944 in
                           Prims.op_Hat uu____8940 uu____8942)) in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8868 uu____8870 uu____8872 uu____8880
           else ());
          r
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu____8961 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____8961 FStar_Pervasives_Native.fst
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_8976 ->
    match uu___21_8976 with
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
      let uu___1259_9025 = p in
      let uu____9028 = whnf tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____9029 = whnf tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1259_9025.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9028;
        FStar_TypeChecker_Common.relation =
          (uu___1259_9025.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9029;
        FStar_TypeChecker_Common.element =
          (uu___1259_9025.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1259_9025.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1259_9025.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1259_9025.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1259_9025.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1259_9025.FStar_TypeChecker_Common.rank)
      }
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv ->
    fun p ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9044 = compress_tprob tcenv p1 in
          FStar_All.pipe_right uu____9044
            (fun uu____9049 -> FStar_TypeChecker_Common.TProb uu____9049)
      | FStar_TypeChecker_Common.CProb uu____9050 -> p
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv ->
    fun pr ->
      let prob =
        let uu____9073 = compress_prob tcenv pr in
        FStar_All.pipe_right uu____9073 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9081 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____9081 with
           | (lh, lhs_args) ->
               let uu____9128 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____9128 with
                | (rh, rhs_args) ->
                    let uu____9175 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9188,
                         FStar_Syntax_Syntax.Tm_uvar uu____9189) ->
                          (match (lhs_args, rhs_args) with
                           | ([], []) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9278 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9305, uu____9306)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9321, FStar_Syntax_Syntax.Tm_uvar uu____9322)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9337,
                         FStar_Syntax_Syntax.Tm_arrow uu____9338) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9368 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_9368.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_9368.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_9368.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_9368.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_9368.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_9368.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_9368.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_9368.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_9368.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9371,
                         FStar_Syntax_Syntax.Tm_type uu____9372) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9388 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_9388.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_9388.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_9388.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_9388.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_9388.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_9388.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_9388.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_9388.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_9388.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type uu____9391,
                         FStar_Syntax_Syntax.Tm_uvar uu____9392) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9408 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_9408.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_9408.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_9408.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_9408.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_9408.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_9408.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_9408.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_9408.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_9408.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9411, FStar_Syntax_Syntax.Tm_uvar uu____9412)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9427, uu____9428)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9443, FStar_Syntax_Syntax.Tm_uvar uu____9444)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9459, uu____9460) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp) in
                    (match uu____9175 with
                     | (rank, tp1) ->
                         let uu____9473 =
                           FStar_All.pipe_right
                             (let uu___1330_9477 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1330_9477.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1330_9477.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1330_9477.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1330_9477.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1330_9477.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1330_9477.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1330_9477.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1330_9477.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1330_9477.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9480 ->
                                FStar_TypeChecker_Common.TProb uu____9480) in
                         (rank, uu____9473))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9484 =
            FStar_All.pipe_right
              (let uu___1334_9488 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1334_9488.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1334_9488.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1334_9488.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1334_9488.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1334_9488.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1334_9488.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1334_9488.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1334_9488.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1334_9488.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9491 -> FStar_TypeChecker_Common.CProb uu____9491) in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9484)
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl ->
    let rec aux uu____9551 probs =
      match uu____9551 with
      | (min_rank, min, out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some p,
                   FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9632 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9653 = rank wl.tcenv hd in
               (match uu____9653 with
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
                      (let uu____9714 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9719 = FStar_Option.get min_rank in
                            rank_less_than rank1 uu____9719) in
                       if uu____9714
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
          let uu____9792 = FStar_Syntax_Util.head_and_args t in
          match uu____9792 with
          | (hd, uu____9811) ->
              let uu____9836 =
                let uu____9837 = FStar_Syntax_Subst.compress hd in
                uu____9837.FStar_Syntax_Syntax.n in
              (match uu____9836 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu____9842) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9877 ->
                           match uu____9877 with
                           | (y, uu____9886) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9909 ->
                                       match uu____9909 with
                                       | (x, uu____9918) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9923 -> false) in
        let uu____9925 = rank tcenv p in
        match uu____9925 with
        | (r, p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9934 -> true
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
    match projectee with | UDeferred _0 -> true | uu____9975 -> false
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | USolved _0 -> true | uu____9994 -> false
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UFailed _0 -> true | uu____10013 -> false
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee -> match projectee with | UFailed _0 -> _0
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s -> let uu____10030 = FStar_Thunk.mkv s in UFailed uu____10030
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s -> let uu____10045 = mklstr s in UFailed uu____10045
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
                        let uu____10096 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____10096 with
                        | (k, uu____10104) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10119 -> false)))
            | uu____10121 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs ->
                      fun uv1 ->
                        let uu____10173 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2 -> FStar_Syntax_Util.eq_univs uv1 uv2)) in
                        if uu____10173 then uv1 :: uvs else uvs) []) in
            let filter =
              FStar_List.filter
                (fun u ->
                   let uu____10197 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u' -> FStar_Syntax_Util.eq_univs u u')) in
                   Prims.op_Negation uu____10197) in
            let uu____10204 = filter u12 in
            let uu____10207 = filter u22 in (uu____10204, uu____10207) in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10242 = filter_out_common_univs us1 us2 in
                   (match uu____10242 with
                    | (us11, us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13, u23::us23) ->
                                let uu____10302 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23 in
                                (match uu____10302 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10305 -> USolved wl1 in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10322 ->
                               let uu____10323 =
                                 FStar_Syntax_Print.univ_to_string u12 in
                               let uu____10325 =
                                 FStar_Syntax_Print.univ_to_string u22 in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10323 uu____10325))
               | (FStar_Syntax_Syntax.U_max us, u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10351 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____10351 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | (u', FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10377 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____10377 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | uu____10380 ->
                   ufailed_thunk
                     (fun uu____10391 ->
                        let uu____10392 =
                          FStar_Syntax_Print.univ_to_string u12 in
                        let uu____10394 =
                          FStar_Syntax_Print.univ_to_string u22 in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10392 uu____10394 msg)) in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10397, uu____10398) ->
              let uu____10400 =
                let uu____10402 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10404 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10402 uu____10404 in
              failwith uu____10400
          | (FStar_Syntax_Syntax.U_unknown, uu____10407) ->
              let uu____10408 =
                let uu____10410 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10412 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10410 uu____10412 in
              failwith uu____10408
          | (uu____10415, FStar_Syntax_Syntax.U_bvar uu____10416) ->
              let uu____10418 =
                let uu____10420 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10422 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10420 uu____10422 in
              failwith uu____10418
          | (uu____10425, FStar_Syntax_Syntax.U_unknown) ->
              let uu____10426 =
                let uu____10428 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10430 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10428 uu____10430 in
              failwith uu____10426
          | (FStar_Syntax_Syntax.U_name x, FStar_Syntax_Syntax.U_name y) ->
              let uu____10435 =
                let uu____10437 = FStar_Ident.string_of_id x in
                let uu____10439 = FStar_Ident.string_of_id y in
                uu____10437 = uu____10439 in
              if uu____10435
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12, FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1, FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10470 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____10470
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu____10489 = occurs_univ v1 u3 in
              if uu____10489
              then
                let uu____10492 =
                  let uu____10494 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____10496 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10494 uu____10496 in
                try_umax_components u11 u21 uu____10492
              else
                (let uu____10501 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____10501)
          | (u, FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____10515 = occurs_univ v1 u3 in
              if uu____10515
              then
                let uu____10518 =
                  let uu____10520 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____10522 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10520 uu____10522 in
                try_umax_components u11 u21 uu____10518
              else
                (let uu____10527 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____10527)
          | (FStar_Syntax_Syntax.U_max uu____10528, uu____10529) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____10537 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____10537
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10543, FStar_Syntax_Syntax.U_max uu____10544) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____10552 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____10552
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____10558,
             FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____10560,
             FStar_Syntax_Syntax.U_name uu____10561) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ
             uu____10563) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name
             uu____10565) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____10567,
             FStar_Syntax_Syntax.U_succ uu____10568) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____10570,
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
      let uu____10677 = bc1 in
      match uu____10677 with
      | (bs1, mk_cod1) ->
          let uu____10721 = bc2 in
          (match uu____10721 with
           | (bs2, mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs, y::ys) ->
                     let uu____10832 = aux xs ys in
                     (match uu____10832 with
                      | ((xs1, xr), (ys1, yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs, ys) ->
                     let uu____10915 =
                       let uu____10922 = mk_cod1 xs in ([], uu____10922) in
                     let uu____10925 =
                       let uu____10932 = mk_cod2 ys in ([], uu____10932) in
                     (uu____10915, uu____10925) in
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
                  let uu____11001 = FStar_Syntax_Syntax.bv_to_name t in
                  FStar_Syntax_Util.mk_has_type t11 uu____11001 t21
              | FStar_Pervasives_Native.None ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11 in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11 in
                  let uu____11004 =
                    let uu____11005 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Util.mk_has_type t11 uu____11005 t21 in
                  FStar_Syntax_Util.mk_forall u_x x uu____11004 in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB ->
                let uu____11010 = has_type_guard t1 t2 in (uu____11010, wl)
            | FStar_TypeChecker_Common.SUBINV ->
                let uu____11011 = has_type_guard t2 t1 in (uu____11011, wl)
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_11018 ->
    match uu___22_11018 with
    | Flex (uu____11020, uu____11021, []) -> true
    | uu____11031 -> false
let (should_defer_flex_to_user_tac :
  FStar_TypeChecker_Env.env -> worklist -> flex_t -> Prims.bool) =
  fun env ->
    fun wl ->
      fun f ->
        let uu____11050 = f in
        match uu____11050 with
        | Flex (uu____11052, u, uu____11054) ->
            let b =
              FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                wl.tcenv u in
            ((let uu____11058 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ResolveImplicitsHook") in
              if uu____11058
              then
                let uu____11063 =
                  FStar_Syntax_Print.ctx_uvar_to_string_no_reason u in
                let uu____11065 = FStar_Util.string_of_bool b in
                FStar_Util.print2
                  "Rel.should_defer_flex_to_user_tac for %s returning %s\n"
                  uu____11063 uu____11065
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
      let uu____11093 = f in
      match uu____11093 with
      | Flex
          (uu____11100,
           { FStar_Syntax_Syntax.ctx_uvar_head = uu____11101;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11102;
             FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
             FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____11105;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____11106;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____11107;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____11108;_},
           args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11174 ->
                 match uu____11174 with
                 | (y, uu____11183) -> FStar_Syntax_Syntax.bv_eq x y) bs in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([], []) ->
                let uu____11337 =
                  let uu____11352 =
                    let uu____11355 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____11355 in
                  ((FStar_List.rev pat_binders), uu____11352) in
                FStar_Pervasives_Native.Some uu____11337
            | (uu____11388, []) ->
                let uu____11419 =
                  let uu____11434 =
                    let uu____11437 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____11437 in
                  ((FStar_List.rev pat_binders), uu____11434) in
                FStar_Pervasives_Native.Some uu____11419
            | ((formal, formal_imp)::formals1, (a, a_imp)::args2) ->
                let uu____11528 =
                  let uu____11529 = FStar_Syntax_Subst.compress a in
                  uu____11529.FStar_Syntax_Syntax.n in
                (match uu____11528 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11549 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders) in
                     if uu____11549
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1675_11579 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1675_11579.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1675_11579.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          } in
                        let subst =
                          let uu____11583 =
                            let uu____11584 =
                              let uu____11591 =
                                FStar_Syntax_Syntax.bv_to_name x1 in
                              (formal, uu____11591) in
                            FStar_Syntax_Syntax.NT uu____11584 in
                          [uu____11583] in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1 in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res in
                        aux
                          (((let uu___1681_11607 = x1 in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1681_11607.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1681_11607.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11608 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([], args2) ->
                let uu____11648 =
                  let uu____11655 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res in
                  FStar_Syntax_Util.arrow_formals uu____11655 in
                (match uu____11648 with
                 | (more_formals, t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11714 ->
                          aux pat_binders more_formals t_res1 args2)) in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11739 ->
               let uu____11740 = FStar_Syntax_Util.arrow_formals t_hd in
               (match uu____11740 with
                | (formals, t_res) -> aux [] formals t_res args))
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env ->
    fun probs ->
      (let uu____12072 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel") in
       if uu____12072
       then
         let uu____12077 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12077
       else ());
      (let uu____12083 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace") in
       if uu____12083
       then
         let uu____12088 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12088
       else ());
      (let uu____12093 = next_prob probs in
       match uu____12093 with
       | FStar_Pervasives_Native.Some (hd, tl, rank1) ->
           let probs1 =
             let uu___1708_12120 = probs in
             {
               attempting = tl;
               wl_deferred = (uu___1708_12120.wl_deferred);
               wl_deferred_to_tac = (uu___1708_12120.wl_deferred_to_tac);
               ctr = (uu___1708_12120.ctr);
               defer_ok = (uu___1708_12120.defer_ok);
               smt_ok = (uu___1708_12120.smt_ok);
               umax_heuristic_ok = (uu___1708_12120.umax_heuristic_ok);
               tcenv = (uu___1708_12120.tcenv);
               wl_implicits = (uu___1708_12120.wl_implicits);
               repr_subcomp_allowed = (uu___1708_12120.repr_subcomp_allowed)
             } in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12129 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs in
                 if uu____12129
                 then
                   let uu____12132 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1 in
                   solve env uu____12132
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
                           (let uu___1720_12144 = tp in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1720_12144.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1720_12144.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1720_12144.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1720_12144.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1720_12144.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1720_12144.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1720_12144.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1720_12144.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1720_12144.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12164 =
                  let uu____12171 = as_deferred probs.wl_deferred_to_tac in
                  ([], uu____12171, (probs.wl_implicits)) in
                Success uu____12164
            | uu____12177 ->
                let uu____12187 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12252 ->
                          match uu____12252 with
                          | (c, uu____12262, uu____12263) -> c < probs.ctr)) in
                (match uu____12187 with
                 | (attempt1, rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12311 =
                            let uu____12318 = as_deferred probs.wl_deferred in
                            let uu____12319 =
                              as_deferred probs.wl_deferred_to_tac in
                            (uu____12318, uu____12319, (probs.wl_implicits)) in
                          Success uu____12311
                      | uu____12320 ->
                          let uu____12330 =
                            let uu___1734_12331 = probs in
                            let uu____12332 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12353 ->
                                      match uu____12353 with
                                      | (uu____12361, uu____12362, y) -> y)) in
                            {
                              attempting = uu____12332;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1734_12331.wl_deferred_to_tac);
                              ctr = (uu___1734_12331.ctr);
                              defer_ok = (uu___1734_12331.defer_ok);
                              smt_ok = (uu___1734_12331.smt_ok);
                              umax_heuristic_ok =
                                (uu___1734_12331.umax_heuristic_ok);
                              tcenv = (uu___1734_12331.tcenv);
                              wl_implicits = (uu___1734_12331.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1734_12331.repr_subcomp_allowed)
                            } in
                          solve env uu____12330))))
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
            let uu____12371 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____12371 with
            | USolved wl1 ->
                let uu____12373 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____12373
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12376 = defer_lit "" orig wl1 in
                solve env uu____12376
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
                  let uu____12427 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____12427 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12430 -> ufailed_simple "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12443;
                  FStar_Syntax_Syntax.vars = uu____12444;_},
                us1),
               FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12447;
                  FStar_Syntax_Syntax.vars = uu____12448;_},
                us2)) ->
                let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12461, uu____12462) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12470, FStar_Syntax_Syntax.Tm_uinst uu____12471) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12479 -> USolved wl
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
            ((let uu____12490 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____12490
              then
                let uu____12495 = prob_to_string env orig in
                let uu____12497 = FStar_Thunk.force msg in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12495 uu____12497
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
            let uu___1816_12512 = wl1 in
            let uu____12513 =
              let uu____12523 =
                let uu____12531 = FStar_Thunk.mkv reason in
                ((wl1.ctr), uu____12531, orig) in
              uu____12523 :: (wl1.wl_deferred_to_tac) in
            {
              attempting = (uu___1816_12512.attempting);
              wl_deferred = (uu___1816_12512.wl_deferred);
              wl_deferred_to_tac = uu____12513;
              ctr = (uu___1816_12512.ctr);
              defer_ok = (uu___1816_12512.defer_ok);
              smt_ok = (uu___1816_12512.smt_ok);
              umax_heuristic_ok = (uu___1816_12512.umax_heuristic_ok);
              tcenv = (uu___1816_12512.tcenv);
              wl_implicits = (uu___1816_12512.wl_implicits);
              repr_subcomp_allowed = (uu___1816_12512.repr_subcomp_allowed)
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
                let uu____12560 = FStar_Syntax_Util.head_and_args t in
                match uu____12560 with
                | (head, uu____12584) ->
                    let uu____12609 =
                      let uu____12610 = FStar_Syntax_Subst.compress head in
                      uu____12610.FStar_Syntax_Syntax.n in
                    (match uu____12609 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv, uu____12620) ->
                         let uu____12637 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv in
                         (uu____12637,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12641 -> (false, "")) in
              let uu____12646 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs in
              (match uu____12646 with
               | (l1, r1) ->
                   let uu____12659 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs in
                   (match uu____12659 with
                    | (l2, r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12676 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl in
                           solve env uu____12676)))
          | uu____12677 ->
              let uu____12678 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl in
              solve env uu____12678
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
               let uu____12764 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements" in
               match uu____12764 with
               | (p, wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3)) in
             let pairwise t1 t2 wl2 =
               (let uu____12819 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu____12819
                then
                  let uu____12824 = FStar_Syntax_Print.term_to_string t1 in
                  let uu____12826 = FStar_Syntax_Print.term_to_string t2 in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12824 uu____12826
                else ());
               (let uu____12831 = head_matches_delta env1 wl2 t1 t2 in
                match uu____12831 with
                | (mr, ts1) ->
                    (match mr with
                     | HeadMatch (true) ->
                         let uu____12877 = eq_prob t1 t2 wl2 in
                         (match uu____12877 with | (p, wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12898 ->
                         let uu____12907 = eq_prob t1 t2 wl2 in
                         (match uu____12907 with | (p, wl3) -> (t1, [p], wl3))
                     | FullMatch ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false) ->
                         let uu____12957 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11, t21) ->
                               let uu____12972 =
                                 FStar_Syntax_Subst.compress t11 in
                               let uu____12973 =
                                 FStar_Syntax_Subst.compress t21 in
                               (uu____12972, uu____12973)
                           | FStar_Pervasives_Native.None ->
                               let uu____12978 =
                                 FStar_Syntax_Subst.compress t1 in
                               let uu____12979 =
                                 FStar_Syntax_Subst.compress t2 in
                               (uu____12978, uu____12979) in
                         (match uu____12957 with
                          | (t11, t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13010 =
                                  FStar_Syntax_Util.head_and_args t12 in
                                match uu____13010 with
                                | (t1_hd, t1_args) ->
                                    let uu____13055 =
                                      FStar_Syntax_Util.head_and_args t22 in
                                    (match uu____13055 with
                                     | (t2_hd, t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13121 =
                                              let uu____13128 =
                                                let uu____13139 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd in
                                                uu____13139 :: t1_args in
                                              let uu____13156 =
                                                let uu____13165 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd in
                                                uu____13165 :: t2_args in
                                              FStar_List.fold_left2
                                                (fun uu____13214 ->
                                                   fun uu____13215 ->
                                                     fun uu____13216 ->
                                                       match (uu____13214,
                                                               uu____13215,
                                                               uu____13216)
                                                       with
                                                       | ((probs, wl4),
                                                          (a1, uu____13266),
                                                          (a2, uu____13268))
                                                           ->
                                                           let uu____13305 =
                                                             eq_prob a1 a2
                                                               wl4 in
                                                           (match uu____13305
                                                            with
                                                            | (p, wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13128
                                                uu____13156 in
                                            match uu____13121 with
                                            | (probs, wl4) ->
                                                let wl' =
                                                  let uu___1919_13331 = wl4 in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1919_13331.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1919_13331.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1919_13331.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1919_13331.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1919_13331.repr_subcomp_allowed)
                                                  } in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____13342 =
                                                  solve env1 wl' in
                                                (match uu____13342 with
                                                 | Success
                                                     (uu____13345,
                                                      defer_to_tac, imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13349 =
                                                         extend_wl wl4
                                                           defer_to_tac imps in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13349))
                                                 | Failed uu____13350 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None)))) in
                              let combine t12 t22 wl3 =
                                let uu____13382 =
                                  base_and_refinement_maybe_delta false env1
                                    t12 in
                                match uu____13382 with
                                | (t1_base, p1_opt) ->
                                    let uu____13418 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22 in
                                    (match uu____13418 with
                                     | (t2_base, p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13517 =
                                               FStar_Syntax_Util.is_t_true t in
                                             if uu____13517
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
                                               let uu____13570 =
                                                 op phi11 phi21 in
                                               refine x1 uu____13570
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
                                               let uu____13602 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____13602
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
                                               let uu____13634 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____13634
                                           | uu____13637 -> t_base in
                                         let uu____13654 =
                                           try_eq t1_base t2_base wl3 in
                                         (match uu____13654 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13668 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt in
                                              (uu____13668, [], wl4)
                                          | FStar_Pervasives_Native.None ->
                                              let uu____13675 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12 in
                                              (match uu____13675 with
                                               | (t1_base1, p1_opt1) ->
                                                   let uu____13711 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22 in
                                                   (match uu____13711 with
                                                    | (t2_base1, p2_opt1) ->
                                                        let uu____13747 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3 in
                                                        (match uu____13747
                                                         with
                                                         | (p, wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1 in
                                                             (t, [p], wl4)))))) in
                              let uu____13771 = combine t11 t21 wl2 in
                              (match uu____13771 with
                               | (t12, ps, wl3) ->
                                   ((let uu____13804 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel") in
                                     if uu____13804
                                     then
                                       let uu____13809 =
                                         FStar_Syntax_Print.term_to_string
                                           t12 in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13809
                                     else ());
                                    (t12, ps, wl3)))))) in
             let rec aux uu____13851 ts1 =
               match uu____13851 with
               | (out, probs, wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13914 = pairwise out t wl2 in
                        (match uu____13914 with
                         | (out1, probs', wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2)) in
             let uu____13950 =
               let uu____13961 = FStar_List.hd ts in (uu____13961, [], wl1) in
             let uu____13970 = FStar_List.tl ts in
             aux uu____13950 uu____13970 in
           let uu____13977 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs)) in
           match uu____13977 with
           | (this_flex, this_rigid) ->
               let uu____14003 =
                 let uu____14004 = FStar_Syntax_Subst.compress this_rigid in
                 uu____14004.FStar_Syntax_Syntax.n in
               (match uu____14003 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs, comp) ->
                    let uu____14029 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp in
                    if uu____14029
                    then
                      let uu____14032 = destruct_flex_t this_flex wl in
                      (match uu____14032 with
                       | (flex, wl1) ->
                           let uu____14039 = quasi_pattern env flex in
                           (match uu____14039 with
                            | FStar_Pervasives_Native.None ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                                ->
                                ((let uu____14058 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____14058
                                  then
                                    let uu____14063 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14063
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14070 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2029_14073 = tp in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2029_14073.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2029_14073.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2029_14073.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2029_14073.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2029_14073.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2029_14073.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2029_14073.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2029_14073.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2029_14073.FStar_TypeChecker_Common.rank)
                                }))] wl in
                       solve env uu____14070)
                | uu____14074 ->
                    ((let uu____14076 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____14076
                      then
                        let uu____14081 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14081
                      else ());
                     (let uu____14086 =
                        FStar_Syntax_Util.head_and_args this_flex in
                      match uu____14086 with
                      | (u, _args) ->
                          let uu____14129 =
                            let uu____14130 = FStar_Syntax_Subst.compress u in
                            uu____14130.FStar_Syntax_Syntax.n in
                          (match uu____14129 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst)
                               ->
                               let equiv t =
                                 let uu____14158 =
                                   FStar_Syntax_Util.head_and_args t in
                                 match uu____14158 with
                                 | (u', uu____14177) ->
                                     let uu____14202 =
                                       let uu____14203 = whnf env u' in
                                       uu____14203.FStar_Syntax_Syntax.n in
                                     (match uu____14202 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar', _subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14225 -> false) in
                               let uu____14227 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_14250 ->
                                         match uu___23_14250 with
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
                                              | uu____14264 -> false)
                                         | uu____14268 -> false)) in
                               (match uu____14227 with
                                | (bounds_probs, rest) ->
                                    let bounds_typs =
                                      let uu____14283 = whnf env this_rigid in
                                      let uu____14284 =
                                        FStar_List.collect
                                          (fun uu___24_14290 ->
                                             match uu___24_14290 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14296 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs in
                                                 [uu____14296]
                                             | uu____14300 -> [])
                                          bounds_probs in
                                      uu____14283 :: uu____14284 in
                                    let uu____14301 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl in
                                    (match uu____14301 with
                                     | (bound, sub_probs, wl1) ->
                                         let uu____14334 =
                                           let flex_u =
                                             flex_uvar_head this_flex in
                                           let bound1 =
                                             let uu____14349 =
                                               let uu____14350 =
                                                 FStar_Syntax_Subst.compress
                                                   bound in
                                               uu____14350.FStar_Syntax_Syntax.n in
                                             match uu____14349 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x, phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14362 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14362)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14373 -> bound in
                                           let uu____14374 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements") in
                                           (bound1, uu____14374) in
                                         (match uu____14334 with
                                          | (bound_typ, (eq_prob, wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14409 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel") in
                                                if uu____14409
                                                then
                                                  let wl'1 =
                                                    let uu___2089_14415 = wl1 in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2089_14415.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2089_14415.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2089_14415.ctr);
                                                      defer_ok =
                                                        (uu___2089_14415.defer_ok);
                                                      smt_ok =
                                                        (uu___2089_14415.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2089_14415.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2089_14415.tcenv);
                                                      wl_implicits =
                                                        (uu___2089_14415.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2089_14415.repr_subcomp_allowed)
                                                    } in
                                                  let uu____14416 =
                                                    wl_to_string wl'1 in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14416
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____14422 =
                                                  solve_t env eq_prob
                                                    (let uu___2094_14424 =
                                                       wl' in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2094_14424.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2094_14424.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2094_14424.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2094_14424.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2094_14424.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2094_14424.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2094_14424.repr_subcomp_allowed)
                                                     }) in
                                                match uu____14422 with
                                                | Success
                                                    (uu____14426,
                                                     defer_to_tac, imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2101_14430 =
                                                        wl' in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2101_14430.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2101_14430.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2101_14430.ctr);
                                                        defer_ok =
                                                          (uu___2101_14430.defer_ok);
                                                        smt_ok =
                                                          (uu___2101_14430.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2101_14430.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2101_14430.tcenv);
                                                        wl_implicits =
                                                          (uu___2101_14430.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2101_14430.repr_subcomp_allowed)
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
                                                    let uu____14447 =
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
                                                    ((let uu____14459 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu____14459
                                                      then
                                                        let uu____14464 =
                                                          let uu____14466 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs) in
                                                          FStar_All.pipe_right
                                                            uu____14466
                                                            (FStar_String.concat
                                                               "\n") in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14464
                                                      else ());
                                                     (let uu____14479 =
                                                        let uu____14494 =
                                                          base_and_refinement
                                                            env bound_typ in
                                                        (rank1, uu____14494) in
                                                      match uu____14479 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          uu____14516)) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14542 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____14542
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
                                                                  let uu____14562
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____14562))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          (x, phi))) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14587 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____14587
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
                                                                    let uu____14607
                                                                    =
                                                                    let uu____14612
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14612 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14607
                                                                    [] wl2 in
                                                                  let uu____14618
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____14618))))
                                                      | uu____14619 ->
                                                          let uu____14634 =
                                                            FStar_Thunk.map
                                                              (fun s ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg in
                                                          giveup env
                                                            uu____14634 p)))))))
                           | uu____14641 when flip ->
                               let uu____14642 =
                                 let uu____14644 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____14646 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14644 uu____14646 in
                               failwith uu____14642
                           | uu____14649 ->
                               let uu____14650 =
                                 let uu____14652 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____14654 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14652 uu____14654 in
                               failwith uu____14650)))))
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
                      (fun uu____14690 ->
                         match uu____14690 with
                         | (x, i) ->
                             let uu____14709 =
                               FStar_Syntax_Syntax.bv_to_name x in
                             (uu____14709, i)) bs_lhs in
                  let uu____14712 = lhs in
                  match uu____14712 with
                  | Flex (uu____14713, u_lhs, uu____14715) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14812 =
                            match uopt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14822 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos in
                                (uu____14822, univ) in
                          match uu____14812 with
                          | (k, univ) ->
                              let uu____14829 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2 in
                              (match uu____14829 with
                               | (uu____14846, u, wl3) ->
                                   let uu____14849 =
                                     f u (FStar_Pervasives_Native.Some univ) in
                                   (uu____14849, wl3)) in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14875 =
                              let uu____14888 =
                                let uu____14899 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                uu____14899 ::
                                  (ct.FStar_Syntax_Syntax.effect_args) in
                              FStar_List.fold_right
                                (fun uu____14950 ->
                                   fun uu____14951 ->
                                     match (uu____14950, uu____14951) with
                                     | ((a, i), (out_args, wl2)) ->
                                         let uu____15052 =
                                           let uu____15059 =
                                             let uu____15062 =
                                               FStar_Syntax_Util.type_u () in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15062 in
                                           copy_uvar u_lhs [] uu____15059 wl2 in
                                         (match uu____15052 with
                                          | (uu____15091, t_a, wl3) ->
                                              let uu____15094 =
                                                copy_uvar u_lhs bs t_a wl3 in
                                              (match uu____15094 with
                                               | (uu____15113, a', wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14888
                                ([], wl1) in
                            (match uu____14875 with
                             | (out_args, wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_15182 ->
                                        match uu___25_15182 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____15184 -> false
                                        | uu____15188 -> true) flags in
                                 let ct' =
                                   let uu___2220_15191 = ct in
                                   let uu____15192 =
                                     let uu____15195 = FStar_List.hd out_args in
                                     FStar_Pervasives_Native.fst uu____15195 in
                                   let uu____15210 = FStar_List.tl out_args in
                                   let uu____15227 =
                                     nodec ct.FStar_Syntax_Syntax.flags in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2220_15191.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2220_15191.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15192;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15210;
                                     FStar_Syntax_Syntax.flags = uu____15227
                                   } in
                                 ((let uu___2223_15231 = c in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2223_15231.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2223_15231.FStar_Syntax_Syntax.vars)
                                   }), wl2)) in
                      let uu____15234 =
                        FStar_Syntax_Util.arrow_formals_comp arrow in
                      (match uu____15234 with
                       | (formals, c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15272 =
                                   imitate_comp bs bs_terms c wl1 in
                                 (match uu____15272 with
                                  | (c', wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c' in
                                      let sol =
                                        let uu____15283 =
                                          let uu____15288 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____15288) in
                                        TERM uu____15283 in
                                      let uu____15289 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation" in
                                      (match uu____15289 with
                                       | (sub_prob, wl3) ->
                                           let uu____15303 =
                                             let uu____15304 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3 in
                                             attempt [sub_prob] uu____15304 in
                                           solve env uu____15303))
                             | (x, imp)::formals2 ->
                                 let uu____15326 =
                                   let uu____15333 =
                                     let uu____15336 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_right uu____15336
                                       FStar_Pervasives_Native.fst in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15333 wl1 in
                                 (match uu____15326 with
                                  | (_ctx_u_x, u_x, wl2) ->
                                      let y =
                                        let uu____15357 =
                                          let uu____15360 =
                                            FStar_Syntax_Syntax.range_of_bv x in
                                          FStar_Pervasives_Native.Some
                                            uu____15360 in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15357 u_x in
                                      let uu____15361 =
                                        let uu____15364 =
                                          let uu____15367 =
                                            let uu____15368 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y in
                                            (uu____15368, imp) in
                                          [uu____15367] in
                                        FStar_List.append bs_terms
                                          uu____15364 in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15361 formals2 wl2) in
                           let uu____15395 = occurs_check u_lhs arrow in
                           (match uu____15395 with
                            | (uu____15408, occurs_ok, msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15424 =
                                    mklstr
                                      (fun uu____15429 ->
                                         let uu____15430 =
                                           FStar_Option.get msg in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15430) in
                                  giveup_or_defer env orig wl uu____15424
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
              (let uu____15463 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____15463
               then
                 let uu____15468 =
                   FStar_Syntax_Print.binders_to_string ", " bs1 in
                 let uu____15471 =
                   FStar_Syntax_Print.binders_to_string ", " bs2 in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15468 (rel_to_string (p_rel orig)) uu____15471
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([], []) ->
                     let uu____15602 = rhs wl1 scope env1 subst in
                     (match uu____15602 with
                      | (rhs_prob, wl2) ->
                          ((let uu____15625 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel") in
                            if uu____15625
                            then
                              let uu____15630 = prob_to_string env1 rhs_prob in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15630
                            else ());
                           (let formula = p_guard rhs_prob in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1, imp)::xs1, (hd2, imp')::ys1) when
                     let uu____15708 = FStar_Syntax_Util.eq_aqual imp imp' in
                     uu____15708 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2293_15710 = hd1 in
                       let uu____15711 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2293_15710.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2293_15710.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15711
                       } in
                     let hd21 =
                       let uu___2296_15715 = hd2 in
                       let uu____15716 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2296_15715.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2296_15715.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15716
                       } in
                     let uu____15719 =
                       let uu____15724 =
                         FStar_All.pipe_left invert_rel (p_rel orig) in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15724
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter" in
                     (match uu____15719 with
                      | (prob, wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                          let subst1 =
                            let uu____15747 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15747 in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                          let uu____15754 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1 in
                          (match uu____15754 with
                           | (env3, FStar_Util.Inl (sub_probs, phi), wl3) ->
                               let phi1 =
                                 let uu____15826 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15826 in
                               ((let uu____15844 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel") in
                                 if uu____15844
                                 then
                                   let uu____15849 =
                                     FStar_Syntax_Print.term_to_string phi1 in
                                   let uu____15851 =
                                     FStar_Syntax_Print.bv_to_string hd12 in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15849
                                     uu____15851
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____15886 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1) in
               let uu____15922 = aux wl [] env [] bs1 bs2 in
               match uu____15922 with
               | (env1, FStar_Util.Inr msg, wl1) -> giveup_lit env1 msg orig
               | (env1, FStar_Util.Inl (sub_probs, phi), wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1 in
                   let uu____15981 = attempt sub_probs wl2 in
                   solve env1 uu____15981)
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
            let uu___2334_16001 = wl in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2334_16001.wl_deferred_to_tac);
              ctr = (uu___2334_16001.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2334_16001.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2334_16001.repr_subcomp_allowed)
            } in
          let tx = FStar_Syntax_Unionfind.new_transaction () in
          let uu____16013 = try_solve env wl' in
          match uu____16013 with
          | Success (uu____16014, defer_to_tac, imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps in solve env wl1))
          | Failed (p, s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16027 = compress_tprob wl.tcenv problem in
         solve_t' env uu____16027 wl)
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
            let uu____16033 = should_defer_flex_to_user_tac env wl lhs in
            if uu____16033
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16046 =
                   FStar_List.map FStar_Pervasives_Native.fst bs in
                 FStar_Util.as_set uu____16046 FStar_Syntax_Syntax.order_bv in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16080 = lhs1 in
                 match uu____16080 with
                 | Flex (uu____16083, ctx_u, uu____16085) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16093 ->
                           let uu____16094 = sn_binders env1 bs in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16094 rhs1 in
                     [TERM (ctx_u, sol)] in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16143 = quasi_pattern env1 lhs1 in
                 match uu____16143 with
                 | FStar_Pervasives_Native.None ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs, uu____16177) ->
                     let uu____16182 = lhs1 in
                     (match uu____16182 with
                      | Flex (t_lhs, ctx_u, args) ->
                          let uu____16197 = occurs_check ctx_u rhs1 in
                          (match uu____16197 with
                           | (uvars, occurs_ok, msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16248 =
                                   let uu____16256 =
                                     let uu____16258 = FStar_Option.get msg in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16258 in
                                   FStar_Util.Inl uu____16256 in
                                 (uu____16248, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs) in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1 in
                                  let uu____16286 =
                                    let uu____16288 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs in
                                    Prims.op_Negation uu____16288 in
                                  if uu____16286
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16315 =
                                       let uu____16323 =
                                         mk_solution env1 lhs1 bs rhs1 in
                                       FStar_Util.Inr uu____16323 in
                                     let uu____16329 =
                                       restrict_all_uvars ctx_u uvars wl1 in
                                     (uu____16315, uu____16329))))) in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16373 = FStar_Syntax_Util.head_and_args rhs1 in
                 match uu____16373 with
                 | (rhs_hd, args) ->
                     let uu____16416 = FStar_Util.prefix args in
                     (match uu____16416 with
                      | (args_rhs, last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              rhs1.FStar_Syntax_Syntax.pos in
                          let uu____16486 = lhs1 in
                          (match uu____16486 with
                           | Flex (t_lhs, u_lhs, _lhs_args) ->
                               let uu____16490 =
                                 let uu____16501 =
                                   let uu____16508 =
                                     let uu____16511 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16511 in
                                   copy_uvar u_lhs [] uu____16508 wl1 in
                                 match uu____16501 with
                                 | (uu____16538, t_last_arg, wl2) ->
                                     let uu____16541 =
                                       let uu____16548 =
                                         let uu____16549 =
                                           let uu____16558 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg in
                                           [uu____16558] in
                                         FStar_List.append bs_lhs uu____16549 in
                                       copy_uvar u_lhs uu____16548 t_res_lhs
                                         wl2 in
                                     (match uu____16541 with
                                      | (uu____16593, lhs', wl3) ->
                                          let uu____16596 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3 in
                                          (match uu____16596 with
                                           | (uu____16613, lhs'_last_arg,
                                              wl4) ->
                                               (lhs', lhs'_last_arg, wl4))) in
                               (match uu____16490 with
                                | (lhs', lhs'_last_arg, wl2) ->
                                    let sol =
                                      let uu____16634 =
                                        let uu____16635 =
                                          let uu____16640 =
                                            let uu____16641 =
                                              let uu____16644 =
                                                let uu____16645 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    lhs'_last_arg in
                                                [uu____16645] in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                lhs' uu____16644
                                                t_lhs.FStar_Syntax_Syntax.pos in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16641
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____16640) in
                                        TERM uu____16635 in
                                      [uu____16634] in
                                    let uu____16670 =
                                      let uu____16677 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs" in
                                      match uu____16677 with
                                      | (p1, wl3) ->
                                          let uu____16697 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs" in
                                          (match uu____16697 with
                                           | (p2, wl4) -> ([p1; p2], wl4)) in
                                    (match uu____16670 with
                                     | (sub_probs, wl3) ->
                                         let uu____16729 =
                                           let uu____16730 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3 in
                                           attempt sub_probs uu____16730 in
                                         solve env1 uu____16729)))) in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16764 = FStar_Syntax_Util.head_and_args rhs2 in
                   match uu____16764 with
                   | (uu____16782, args) ->
                       (match args with | [] -> false | uu____16818 -> true) in
                 let is_arrow rhs2 =
                   let uu____16837 =
                     let uu____16838 = FStar_Syntax_Subst.compress rhs2 in
                     uu____16838.FStar_Syntax_Syntax.n in
                   match uu____16837 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____16842 -> true
                   | uu____16858 -> false in
                 let uu____16860 = quasi_pattern env1 lhs1 in
                 match uu____16860 with
                 | FStar_Pervasives_Native.None ->
                     let msg =
                       mklstr
                         (fun uu____16879 ->
                            let uu____16880 = prob_to_string env1 orig1 in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____16880) in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                     let uu____16889 = is_app rhs1 in
                     if uu____16889
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____16894 = is_arrow rhs1 in
                        if uu____16894
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu____16907 ->
                                  let uu____16908 = prob_to_string env1 orig1 in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____16908) in
                           giveup_or_defer env1 orig1 wl1 msg)) in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB ->
                   if wl.defer_ok
                   then
                     let uu____16912 = FStar_Thunk.mkv "flex-rigid subtyping" in
                     giveup_or_defer env orig wl uu____16912
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV ->
                   if wl.defer_ok
                   then
                     let uu____16918 = FStar_Thunk.mkv "flex-rigid subtyping" in
                     giveup_or_defer env orig wl uu____16918
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ ->
                   let uu____16923 = lhs in
                   (match uu____16923 with
                    | Flex (_t1, ctx_uv, args_lhs) ->
                        let uu____16927 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs in
                        (match uu____16927 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs in
                             let names_to_string1 fvs =
                               let uu____16945 =
                                 let uu____16949 =
                                   FStar_Util.set_elements fvs in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____16949 in
                               FStar_All.pipe_right uu____16945
                                 (FStar_String.concat ", ") in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders) in
                             let fvs2 = FStar_Syntax_Free.names rhs1 in
                             let uu____16970 = occurs_check ctx_uv rhs1 in
                             (match uu____16970 with
                              | (uvars, occurs_ok, msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____16999 =
                                      let uu____17000 =
                                        let uu____17002 =
                                          FStar_Option.get msg in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17002 in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17000 in
                                    giveup_or_defer env orig wl uu____16999
                                  else
                                    (let uu____17010 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1 in
                                     if uu____17010
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1 in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars wl in
                                       let uu____17017 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1 in
                                       solve env uu____17017
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            mklstr
                                              (fun uu____17033 ->
                                                 let uu____17034 =
                                                   names_to_string1 fvs2 in
                                                 let uu____17036 =
                                                   names_to_string1 fvs1 in
                                                 let uu____17038 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders) in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17034 uu____17036
                                                   uu____17038) in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17050 ->
                             if wl.defer_ok
                             then
                               let uu____17054 =
                                 FStar_Thunk.mkv "Not a pattern" in
                               giveup_or_defer env orig wl uu____17054
                             else
                               (let uu____17059 =
                                  try_quasi_pattern orig env wl lhs rhs in
                                match uu____17059 with
                                | (FStar_Util.Inr sol, wl1) ->
                                    let uu____17085 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1 in
                                    solve env uu____17085
                                | (FStar_Util.Inl msg, uu____17087) ->
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
                  let uu____17105 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____17105
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV ->
                if wl.defer_ok
                then
                  let uu____17111 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____17111
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ ->
                let uu____17116 =
                  (should_defer_flex_to_user_tac env wl lhs) ||
                    (should_defer_flex_to_user_tac env wl rhs) in
                if uu____17116
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
                    (let uu____17123 =
                       FStar_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer env orig wl uu____17123)
                  else
                    (let uu____17128 =
                       let uu____17145 = quasi_pattern env lhs in
                       let uu____17152 = quasi_pattern env rhs in
                       (uu____17145, uu____17152) in
                     match uu____17128 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs, t_res_lhs),
                        FStar_Pervasives_Native.Some
                        (binders_rhs, t_res_rhs)) ->
                         let uu____17195 = lhs in
                         (match uu____17195 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17196;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17198;_},
                               u_lhs, uu____17200)
                              ->
                              let uu____17203 = rhs in
                              (match uu____17203 with
                               | Flex (uu____17204, u_rhs, uu____17206) ->
                                   let uu____17207 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs) in
                                   if uu____17207
                                   then
                                     let uu____17214 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl in
                                     solve env uu____17214
                                   else
                                     (let uu____17217 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders in
                                      match uu____17217 with
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
                                          let uu____17249 =
                                            let uu____17256 =
                                              let uu____17259 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17259 in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____17256
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
                                          (match uu____17249 with
                                           | (uu____17268, w, wl1) ->
                                               let w_app =
                                                 let uu____17272 =
                                                   FStar_List.map
                                                     (fun uu____17283 ->
                                                        match uu____17283
                                                        with
                                                        | (z, uu____17291) ->
                                                            let uu____17296 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____17296) zs in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____17272
                                                   w.FStar_Syntax_Syntax.pos in
                                               ((let uu____17298 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____17298
                                                 then
                                                   let uu____17303 =
                                                     let uu____17307 =
                                                       flex_t_to_string lhs in
                                                     let uu____17309 =
                                                       let uu____17313 =
                                                         flex_t_to_string rhs in
                                                       let uu____17315 =
                                                         let uu____17319 =
                                                           term_to_string w in
                                                         let uu____17321 =
                                                           let uu____17325 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs) in
                                                           let uu____17334 =
                                                             let uu____17338
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs) in
                                                             let uu____17347
                                                               =
                                                               let uu____17351
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs in
                                                               [uu____17351] in
                                                             uu____17338 ::
                                                               uu____17347 in
                                                           uu____17325 ::
                                                             uu____17334 in
                                                         uu____17319 ::
                                                           uu____17321 in
                                                       uu____17313 ::
                                                         uu____17315 in
                                                     uu____17307 ::
                                                       uu____17309 in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17303
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17368 =
                                                       let uu____17373 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs)) in
                                                       (u_lhs, uu____17373) in
                                                     TERM uu____17368 in
                                                   let uu____17374 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   if uu____17374
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17382 =
                                                          let uu____17387 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          (u_rhs,
                                                            uu____17387) in
                                                        TERM uu____17382 in
                                                      [s1; s2]) in
                                                 let uu____17388 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1 in
                                                 solve env uu____17388))))))
                     | uu____17389 ->
                         let uu____17406 =
                           FStar_Thunk.mkv "flex-flex: non-patterns" in
                         giveup_or_defer env orig wl uu____17406)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____17460 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu____17460
            then
              let uu____17465 = FStar_Syntax_Print.term_to_string t1 in
              let uu____17467 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____17469 = FStar_Syntax_Print.term_to_string t2 in
              let uu____17471 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17465 uu____17467 uu____17469 uu____17471
            else ());
           (let uu____17482 = FStar_Syntax_Util.head_and_args t1 in
            match uu____17482 with
            | (head1, args1) ->
                let uu____17525 = FStar_Syntax_Util.head_and_args t2 in
                (match uu____17525 with
                 | (head2, args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17595 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu____17595 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17600 =
                                defer_lit "universe constraints" orig wl3 in
                              k false uu____17600) in
                     let nargs = FStar_List.length args1 in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17621 =
                         mklstr
                           (fun uu____17632 ->
                              let uu____17633 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____17635 = args_to_string args1 in
                              let uu____17639 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu____17641 = args_to_string args2 in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17633 uu____17635 uu____17639
                                uu____17641) in
                       giveup env1 uu____17621 orig
                     else
                       (let uu____17648 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17653 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu____17653 = FStar_Syntax_Util.Equal) in
                        if uu____17648
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2607_17657 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2607_17657.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2607_17657.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2607_17657.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2607_17657.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2607_17657.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2607_17657.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2607_17657.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2607_17657.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu____17667 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu____17667
                                    else solve env1 wl2))
                        else
                          (let uu____17672 = base_and_refinement env1 t1 in
                           match uu____17672 with
                           | (base1, refinement1) ->
                               let uu____17697 = base_and_refinement env1 t2 in
                               (match uu____17697 with
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
                                           let uu____17862 =
                                             FStar_List.fold_right
                                               (fun uu____17902 ->
                                                  fun uu____17903 ->
                                                    match (uu____17902,
                                                            uu____17903)
                                                    with
                                                    | (((a1, uu____17955),
                                                        (a2, uu____17957)),
                                                       (probs, wl3)) ->
                                                        let uu____18006 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu____18006
                                                         with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu____17862 with
                                           | (subprobs, wl3) ->
                                               ((let uu____18049 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____18049
                                                 then
                                                   let uu____18054 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18054
                                                 else ());
                                                (let uu____18060 =
                                                   FStar_Options.defensive () in
                                                 if uu____18060
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
                                                    (let uu____18087 =
                                                       mk_sub_probs wl3 in
                                                     match uu____18087 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu____18103 =
                                                             FStar_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18103 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu____18111 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2
                                                           uu____18111)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu____18136 =
                                                    mk_sub_probs wl3 in
                                                  match uu____18136 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu____18152 =
                                                          FStar_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18152 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu____18160 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu____18160) in
                                         let unfold_and_retry d env2 wl2
                                           uu____18188 =
                                           match uu____18188 with
                                           | (prob, reason) ->
                                               ((let uu____18205 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____18205
                                                 then
                                                   let uu____18210 =
                                                     prob_to_string env2 orig in
                                                   let uu____18212 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____18210 uu____18212
                                                 else ());
                                                (let uu____18218 =
                                                   let uu____18227 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu____18230 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu____18227, uu____18230) in
                                                 match uu____18218 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18243 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu____18243 with
                                                      | (head1', uu____18261)
                                                          ->
                                                          let uu____18286 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu____18286
                                                           with
                                                           | (head2',
                                                              uu____18304) ->
                                                               let uu____18329
                                                                 =
                                                                 let uu____18334
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu____18335
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu____18334,
                                                                   uu____18335) in
                                                               (match uu____18329
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
                                                                    let uu____18337
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____18337
                                                                    then
                                                                    let uu____18342
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____18344
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu____18346
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____18348
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18342
                                                                    uu____18344
                                                                    uu____18346
                                                                    uu____18348
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18353
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2695_18361
                                                                    = torig in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2695_18361.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2695_18361.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2695_18361.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2695_18361.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2695_18361.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2695_18361.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2695_18361.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2695_18361.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
                                                                    let uu____18363
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____18363
                                                                    then
                                                                    let uu____18368
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18368
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18373 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu____18385 =
                                             delta_depth_of_term env1 head1 in
                                           match uu____18385 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d in
                                         let treat_as_injective =
                                           let uu____18393 =
                                             let uu____18394 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu____18394.FStar_Syntax_Syntax.n in
                                           match uu____18393 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18399 -> false in
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
                                          | uu____18402 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18405 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t env1
                                           (let uu___2715_18441 = problem in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2715_18441.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2715_18441.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2715_18441.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2715_18441.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2715_18441.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2715_18441.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2715_18441.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2715_18441.FStar_TypeChecker_Common.rank)
                                            }) wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18517 = destruct_flex_t scrutinee wl1 in
             match uu____18517 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu____18528 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p in
                 (match uu____18528 with
                  | (xs, pat_term, uu____18544, uu____18545) ->
                      let uu____18550 =
                        FStar_List.fold_left
                          (fun uu____18573 ->
                             fun x ->
                               match uu____18573 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____18594 = copy_uvar uv [] t_x wl3 in
                                   (match uu____18594 with
                                    | (uu____18613, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu____18550 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu____18634 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic" in
                           (match uu____18634 with
                            | (prob, wl4) ->
                                let wl' =
                                  let uu___2756_18651 = wl4 in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2756_18651.wl_deferred_to_tac);
                                    ctr = (uu___2756_18651.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2756_18651.umax_heuristic_ok);
                                    tcenv = (uu___2756_18651.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2756_18651.repr_subcomp_allowed)
                                  } in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let uu____18662 = solve env1 wl' in
                                (match uu____18662 with
                                 | Success (uu____18665, defer_to_tac, imps)
                                     ->
                                     let wl'1 =
                                       let uu___2765_18669 = wl' in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2765_18669.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2765_18669.wl_deferred_to_tac);
                                         ctr = (uu___2765_18669.ctr);
                                         defer_ok =
                                           (uu___2765_18669.defer_ok);
                                         smt_ok = (uu___2765_18669.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2765_18669.umax_heuristic_ok);
                                         tcenv = (uu___2765_18669.tcenv);
                                         wl_implicits =
                                           (uu___2765_18669.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2765_18669.repr_subcomp_allowed)
                                       } in
                                     let uu____18670 = solve env1 wl'1 in
                                     (match uu____18670 with
                                      | Success
                                          (uu____18673, defer_to_tac', imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18677 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps') in
                                            FStar_Pervasives_Native.Some
                                              uu____18677))
                                      | Failed uu____18683 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18689 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None))))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu____18712 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu____18712
                 then
                   let uu____18717 = FStar_Syntax_Print.term_to_string t1 in
                   let uu____18719 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18717 uu____18719
                 else ());
                (let uu____18724 =
                   let uu____18745 =
                     let uu____18754 = FStar_Syntax_Util.unmeta t1 in
                     (s1, uu____18754) in
                   let uu____18761 =
                     let uu____18770 = FStar_Syntax_Util.unmeta t2 in
                     (s2, uu____18770) in
                   (uu____18745, uu____18761) in
                 match uu____18724 with
                 | ((uu____18800,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____18803;
                       FStar_Syntax_Syntax.vars = uu____18804;_}),
                    (s, t)) ->
                     let uu____18875 =
                       let uu____18877 = is_flex scrutinee in
                       Prims.op_Negation uu____18877 in
                     if uu____18875
                     then
                       ((let uu____18888 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____18888
                         then
                           let uu____18893 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18893
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18912 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18912
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18927 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____18927
                           then
                             let uu____18932 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____18934 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18932 uu____18934
                           else ());
                          (let pat_discriminates uu___26_18959 =
                             match uu___26_18959 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____18975;
                                  FStar_Syntax_Syntax.p = uu____18976;_},
                                FStar_Pervasives_Native.None, uu____18977) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____18991;
                                  FStar_Syntax_Syntax.p = uu____18992;_},
                                FStar_Pervasives_Native.None, uu____18993) ->
                                 true
                             | uu____19020 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____19123 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____19123 with
                                       | (uu____19125, uu____19126, t') ->
                                           let uu____19144 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____19144 with
                                            | (FullMatch, uu____19156) ->
                                                true
                                            | (HeadMatch uu____19170,
                                               uu____19171) -> true
                                            | uu____19186 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____19223 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____19223
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19234 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____19234 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____19322, uu____19323)
                                       -> branches1
                                   | uu____19468 -> branches in
                                 let uu____19523 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____19532 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____19532 with
                                        | (p, uu____19536, uu____19537) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____19566 ->
                                      FStar_Util.Inr uu____19566) uu____19523))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19596 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____19596 with
                                | (p, uu____19605, e) ->
                                    ((let uu____19624 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____19624
                                      then
                                        let uu____19629 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____19631 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19629 uu____19631
                                      else ());
                                     (let uu____19636 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____19651 ->
                                           FStar_Util.Inr uu____19651)
                                        uu____19636)))))
                 | ((s, t),
                    (uu____19654,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____19657;
                       FStar_Syntax_Syntax.vars = uu____19658;_}))
                     ->
                     let uu____19727 =
                       let uu____19729 = is_flex scrutinee in
                       Prims.op_Negation uu____19729 in
                     if uu____19727
                     then
                       ((let uu____19740 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____19740
                         then
                           let uu____19745 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19745
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19764 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19764
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19779 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19779
                           then
                             let uu____19784 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____19786 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19784 uu____19786
                           else ());
                          (let pat_discriminates uu___26_19811 =
                             match uu___26_19811 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19827;
                                  FStar_Syntax_Syntax.p = uu____19828;_},
                                FStar_Pervasives_Native.None, uu____19829) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19843;
                                  FStar_Syntax_Syntax.p = uu____19844;_},
                                FStar_Pervasives_Native.None, uu____19845) ->
                                 true
                             | uu____19872 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____19975 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____19975 with
                                       | (uu____19977, uu____19978, t') ->
                                           let uu____19996 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____19996 with
                                            | (FullMatch, uu____20008) ->
                                                true
                                            | (HeadMatch uu____20022,
                                               uu____20023) -> true
                                            | uu____20038 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____20075 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____20075
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20086 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____20086 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____20174, uu____20175)
                                       -> branches1
                                   | uu____20320 -> branches in
                                 let uu____20375 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____20384 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____20384 with
                                        | (p, uu____20388, uu____20389) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____20418 ->
                                      FStar_Util.Inr uu____20418) uu____20375))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20448 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____20448 with
                                | (p, uu____20457, e) ->
                                    ((let uu____20476 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____20476
                                      then
                                        let uu____20481 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____20483 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20481 uu____20483
                                      else ());
                                     (let uu____20488 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____20503 ->
                                           FStar_Util.Inr uu____20503)
                                        uu____20488)))))
                 | uu____20504 ->
                     ((let uu____20526 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu____20526
                       then
                         let uu____20531 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____20533 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20531 uu____20533
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____20579 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu____20579
            then
              let uu____20584 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____20586 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____20588 = FStar_Syntax_Print.term_to_string t1 in
              let uu____20590 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20584 uu____20586 uu____20588 uu____20590
            else ());
           (let uu____20595 = head_matches_delta env1 wl1 t1 t2 in
            match uu____20595 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu____20626, uu____20627) ->
                     let rec may_relate head =
                       let uu____20655 =
                         let uu____20656 = FStar_Syntax_Subst.compress head in
                         uu____20656.FStar_Syntax_Syntax.n in
                       match uu____20655 with
                       | FStar_Syntax_Syntax.Tm_name uu____20660 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20662 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20687 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv in
                           (match uu____20687 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20689 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20692
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20693 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t, uu____20696, uu____20697) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t, uu____20739) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t, uu____20745) ->
                           may_relate t
                       | uu____20750 -> false in
                     let uu____20752 =
                       try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu____20752 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20765 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig uu____20765
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None) ->
                          let uu____20775 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok in
                          if uu____20775
                          then
                            let uu____20778 =
                              guard_of_prob env1 wl1 problem t1 t2 in
                            (match uu____20778 with
                             | (guard, wl2) ->
                                 let uu____20785 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2 in
                                 solve env1 uu____20785)
                          else
                            (let uu____20788 =
                               mklstr
                                 (fun uu____20799 ->
                                    let uu____20800 =
                                      FStar_Syntax_Print.term_to_string head1 in
                                    let uu____20802 =
                                      let uu____20804 =
                                        let uu____20808 =
                                          delta_depth_of_term env1 head1 in
                                        FStar_Util.bind_opt uu____20808
                                          (fun x ->
                                             let uu____20815 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____20815) in
                                      FStar_Util.dflt "" uu____20804 in
                                    let uu____20820 =
                                      FStar_Syntax_Print.term_to_string head2 in
                                    let uu____20822 =
                                      let uu____20824 =
                                        let uu____20828 =
                                          delta_depth_of_term env1 head2 in
                                        FStar_Util.bind_opt uu____20828
                                          (fun x ->
                                             let uu____20835 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____20835) in
                                      FStar_Util.dflt "" uu____20824 in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20800 uu____20802 uu____20820
                                      uu____20822) in
                             giveup env1 uu____20788 orig))
                 | (HeadMatch (true), uu____20841) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20856 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu____20856 with
                        | (guard, wl2) ->
                            let uu____20863 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu____20863)
                     else
                       (let uu____20866 =
                          mklstr
                            (fun uu____20873 ->
                               let uu____20874 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____20876 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20874 uu____20876) in
                        giveup env1 uu____20866 orig)
                 | (uu____20879, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       (let uu___2947_20893 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2947_20893.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2947_20893.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2947_20893.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2947_20893.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2947_20893.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2947_20893.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2947_20893.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2947_20893.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____20920 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____20920
          then
            let uu____20923 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____20923
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu____20929 =
                let uu____20932 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____20932 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20929 t1);
             (let uu____20951 =
                let uu____20954 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____20954 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20951 t2);
             (let uu____20973 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu____20973
              then
                let uu____20977 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu____20979 =
                  let uu____20981 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu____20983 =
                    let uu____20985 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu____20985 in
                  Prims.op_Hat uu____20981 uu____20983 in
                let uu____20988 =
                  let uu____20990 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu____20992 =
                    let uu____20994 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu____20994 in
                  Prims.op_Hat uu____20990 uu____20992 in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____20977 uu____20979 uu____20988
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21001, uu____21002) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21018, FStar_Syntax_Syntax.Tm_delayed uu____21019) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21035, uu____21036) ->
                  let uu____21063 =
                    let uu___2978_21064 = problem in
                    let uu____21065 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2978_21064.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21065;
                      FStar_TypeChecker_Common.relation =
                        (uu___2978_21064.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2978_21064.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2978_21064.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2978_21064.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2978_21064.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2978_21064.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2978_21064.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2978_21064.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21063 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21066, uu____21067) ->
                  let uu____21074 =
                    let uu___2984_21075 = problem in
                    let uu____21076 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2984_21075.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21076;
                      FStar_TypeChecker_Common.relation =
                        (uu___2984_21075.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2984_21075.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2984_21075.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2984_21075.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2984_21075.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2984_21075.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2984_21075.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2984_21075.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21074 wl
              | (uu____21077, FStar_Syntax_Syntax.Tm_ascribed uu____21078) ->
                  let uu____21105 =
                    let uu___2990_21106 = problem in
                    let uu____21107 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2990_21106.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2990_21106.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2990_21106.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21107;
                      FStar_TypeChecker_Common.element =
                        (uu___2990_21106.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2990_21106.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2990_21106.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2990_21106.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2990_21106.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2990_21106.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21105 wl
              | (uu____21108, FStar_Syntax_Syntax.Tm_meta uu____21109) ->
                  let uu____21116 =
                    let uu___2996_21117 = problem in
                    let uu____21118 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2996_21117.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2996_21117.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2996_21117.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21118;
                      FStar_TypeChecker_Common.element =
                        (uu___2996_21117.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2996_21117.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2996_21117.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2996_21117.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2996_21117.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2996_21117.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21116 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____21120),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu____21122)) ->
                  let uu____21131 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu____21131
              | (FStar_Syntax_Syntax.Tm_bvar uu____21132, uu____21133) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21135, FStar_Syntax_Syntax.Tm_bvar uu____21136) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___27_21206 =
                    match uu___27_21206 with
                    | [] -> c
                    | bs ->
                        let uu____21234 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu____21234 in
                  let uu____21245 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu____21245 with
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
                                    let uu____21394 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu____21394
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___28_21483 =
                    match uu___28_21483 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu____21525 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu____21525 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu____21670 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu____21671 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu____21670
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21671 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21673, uu____21674) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21705 -> true
                    | uu____21725 -> false in
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
                      (let uu____21785 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3098_21793 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3098_21793.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3098_21793.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3098_21793.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3098_21793.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3098_21793.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3098_21793.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3098_21793.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3098_21793.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3098_21793.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3098_21793.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3098_21793.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3098_21793.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3098_21793.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3098_21793.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3098_21793.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3098_21793.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3098_21793.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3098_21793.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3098_21793.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3098_21793.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3098_21793.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3098_21793.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3098_21793.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3098_21793.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3098_21793.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3098_21793.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3098_21793.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3098_21793.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3098_21793.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3098_21793.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3098_21793.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3098_21793.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3098_21793.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3098_21793.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3098_21793.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3098_21793.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3098_21793.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3098_21793.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3098_21793.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3098_21793.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3098_21793.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3098_21793.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3098_21793.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3098_21793.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____21785 with
                       | (uu____21798, ty, uu____21800) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____21809 =
                                 let uu____21810 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____21810.FStar_Syntax_Syntax.n in
                               match uu____21809 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21813 ->
                                   let uu____21820 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____21820
                               | uu____21821 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____21824 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____21824
                             then
                               let uu____21829 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____21831 =
                                 let uu____21833 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21833 in
                               let uu____21834 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21829 uu____21831 uu____21834
                             else ());
                            r1)) in
                  let uu____21839 =
                    let uu____21856 = maybe_eta t1 in
                    let uu____21863 = maybe_eta t2 in
                    (uu____21856, uu____21863) in
                  (match uu____21839 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3119_21905 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3119_21905.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3119_21905.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3119_21905.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3119_21905.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3119_21905.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3119_21905.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3119_21905.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3119_21905.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____21926 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____21926
                       then
                         let uu____21929 = destruct_flex_t not_abs wl in
                         (match uu____21929 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_21946 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_21946.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_21946.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_21946.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_21946.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_21946.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_21946.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_21946.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_21946.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21949 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____21949 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____21972 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____21972
                       then
                         let uu____21975 = destruct_flex_t not_abs wl in
                         (match uu____21975 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_21992 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_21992.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_21992.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_21992.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_21992.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_21992.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_21992.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_21992.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_21992.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21995 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____21995 orig))
                   | uu____21998 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22016, FStar_Syntax_Syntax.Tm_abs uu____22017) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22048 -> true
                    | uu____22068 -> false in
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
                      (let uu____22128 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3098_22136 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3098_22136.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3098_22136.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3098_22136.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3098_22136.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3098_22136.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3098_22136.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3098_22136.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3098_22136.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3098_22136.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3098_22136.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3098_22136.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3098_22136.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3098_22136.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3098_22136.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3098_22136.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3098_22136.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3098_22136.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3098_22136.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3098_22136.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3098_22136.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3098_22136.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3098_22136.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3098_22136.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3098_22136.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3098_22136.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3098_22136.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3098_22136.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3098_22136.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3098_22136.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3098_22136.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3098_22136.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3098_22136.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3098_22136.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3098_22136.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3098_22136.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3098_22136.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3098_22136.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3098_22136.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3098_22136.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3098_22136.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3098_22136.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3098_22136.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3098_22136.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3098_22136.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____22128 with
                       | (uu____22141, ty, uu____22143) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____22152 =
                                 let uu____22153 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____22153.FStar_Syntax_Syntax.n in
                               match uu____22152 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22156 ->
                                   let uu____22163 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____22163
                               | uu____22164 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____22167 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____22167
                             then
                               let uu____22172 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____22174 =
                                 let uu____22176 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22176 in
                               let uu____22177 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22172 uu____22174 uu____22177
                             else ());
                            r1)) in
                  let uu____22182 =
                    let uu____22199 = maybe_eta t1 in
                    let uu____22206 = maybe_eta t2 in
                    (uu____22199, uu____22206) in
                  (match uu____22182 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3119_22248 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3119_22248.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3119_22248.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3119_22248.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3119_22248.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3119_22248.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3119_22248.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3119_22248.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3119_22248.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____22269 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22269
                       then
                         let uu____22272 = destruct_flex_t not_abs wl in
                         (match uu____22272 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_22289 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_22289.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_22289.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_22289.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_22289.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_22289.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_22289.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_22289.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_22289.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22292 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22292 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____22315 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22315
                       then
                         let uu____22318 = destruct_flex_t not_abs wl in
                         (match uu____22318 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_22335 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_22335.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_22335.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_22335.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_22335.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_22335.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_22335.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_22335.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_22335.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22338 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22338 orig))
                   | uu____22341 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu____22371 =
                    let uu____22376 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu____22376 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ((let uu___3159_22404 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3159_22404.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3159_22404.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3161_22406 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3161_22406.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3161_22406.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22407, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ((let uu___3159_22422 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3159_22422.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3159_22422.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3161_22424 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3161_22424.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3161_22424.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22425 -> (x1, x2) in
                  (match uu____22371 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu____22444 = as_refinement false env t11 in
                       (match uu____22444 with
                        | (x12, phi11) ->
                            let uu____22452 = as_refinement false env t21 in
                            (match uu____22452 with
                             | (x22, phi21) ->
                                 ((let uu____22461 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu____22461
                                   then
                                     ((let uu____22466 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu____22468 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu____22470 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22466
                                         uu____22468 uu____22470);
                                      (let uu____22473 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu____22475 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu____22477 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22473
                                         uu____22475 uu____22477))
                                   else ());
                                  (let uu____22482 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu____22482 with
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
                                         let uu____22553 = imp phi13 phi23 in
                                         FStar_All.pipe_right uu____22553
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu____22565 =
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
                                         (let uu____22578 =
                                            let uu____22581 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22581 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22578
                                            (p_guard base_prob));
                                         (let uu____22600 =
                                            let uu____22603 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22603 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22600
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu____22622 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu____22622) in
                                       let has_uvars =
                                         (let uu____22627 =
                                            let uu____22629 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Util.set_is_empty
                                              uu____22629 in
                                          Prims.op_Negation uu____22627) ||
                                           (let uu____22633 =
                                              let uu____22635 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Util.set_is_empty
                                                uu____22635 in
                                            Prims.op_Negation uu____22633) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22639 =
                                           let uu____22644 =
                                             let uu____22653 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu____22653] in
                                           mk_t_problem wl1 uu____22644 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu____22639 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu____22676 =
                                                solve env1
                                                  (let uu___3204_22678 = wl2 in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3204_22678.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3204_22678.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3204_22678.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3204_22678.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3204_22678.tcenv);
                                                     wl_implicits =
                                                       (uu___3204_22678.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3204_22678.repr_subcomp_allowed)
                                                   }) in
                                              (match uu____22676 with
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
                                                   (uu____22693,
                                                    defer_to_tac,
                                                    uu____22695)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22700 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22700 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       let uu___3220_22709 =
                                                         wl3 in
                                                       {
                                                         attempting =
                                                           (uu___3220_22709.attempting);
                                                         wl_deferred =
                                                           (uu___3220_22709.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3220_22709.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3220_22709.defer_ok);
                                                         smt_ok =
                                                           (uu___3220_22709.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3220_22709.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3220_22709.tcenv);
                                                         wl_implicits =
                                                           (uu___3220_22709.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3220_22709.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac [] in
                                                     let uu____22712 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu____22712))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22715,
                 FStar_Syntax_Syntax.Tm_uvar uu____22716) ->
                  let uu____22741 = ensure_no_uvar_subst t1 wl in
                  (match uu____22741 with
                   | (t11, wl1) ->
                       let uu____22748 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____22748 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22757;
                    FStar_Syntax_Syntax.pos = uu____22758;
                    FStar_Syntax_Syntax.vars = uu____22759;_},
                  uu____22760),
                 FStar_Syntax_Syntax.Tm_uvar uu____22761) ->
                  let uu____22810 = ensure_no_uvar_subst t1 wl in
                  (match uu____22810 with
                   | (t11, wl1) ->
                       let uu____22817 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____22817 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22826,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22827;
                    FStar_Syntax_Syntax.pos = uu____22828;
                    FStar_Syntax_Syntax.vars = uu____22829;_},
                  uu____22830)) ->
                  let uu____22879 = ensure_no_uvar_subst t1 wl in
                  (match uu____22879 with
                   | (t11, wl1) ->
                       let uu____22886 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____22886 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22895;
                    FStar_Syntax_Syntax.pos = uu____22896;
                    FStar_Syntax_Syntax.vars = uu____22897;_},
                  uu____22898),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22899;
                    FStar_Syntax_Syntax.pos = uu____22900;
                    FStar_Syntax_Syntax.vars = uu____22901;_},
                  uu____22902)) ->
                  let uu____22975 = ensure_no_uvar_subst t1 wl in
                  (match uu____22975 with
                   | (t11, wl1) ->
                       let uu____22982 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____22982 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22991, uu____22992) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23005 = destruct_flex_t t1 wl in
                  (match uu____23005 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23012;
                    FStar_Syntax_Syntax.pos = uu____23013;
                    FStar_Syntax_Syntax.vars = uu____23014;_},
                  uu____23015),
                 uu____23016) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23053 = destruct_flex_t t1 wl in
                  (match uu____23053 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23060, FStar_Syntax_Syntax.Tm_uvar uu____23061) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23074, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23075;
                    FStar_Syntax_Syntax.pos = uu____23076;
                    FStar_Syntax_Syntax.vars = uu____23077;_},
                  uu____23078)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____23115,
                 FStar_Syntax_Syntax.Tm_arrow uu____23116) ->
                  solve_t' env
                    (let uu___3323_23144 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3323_23144.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3323_23144.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3323_23144.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3323_23144.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3323_23144.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3323_23144.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3323_23144.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3323_23144.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3323_23144.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23145;
                    FStar_Syntax_Syntax.pos = uu____23146;
                    FStar_Syntax_Syntax.vars = uu____23147;_},
                  uu____23148),
                 FStar_Syntax_Syntax.Tm_arrow uu____23149) ->
                  solve_t' env
                    (let uu___3323_23201 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3323_23201.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3323_23201.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3323_23201.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3323_23201.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3323_23201.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3323_23201.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3323_23201.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3323_23201.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3323_23201.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23202, FStar_Syntax_Syntax.Tm_uvar uu____23203) ->
                  let uu____23216 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23216
              | (uu____23217, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23218;
                    FStar_Syntax_Syntax.pos = uu____23219;
                    FStar_Syntax_Syntax.vars = uu____23220;_},
                  uu____23221)) ->
                  let uu____23258 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23258
              | (FStar_Syntax_Syntax.Tm_uvar uu____23259, uu____23260) ->
                  let uu____23273 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23273
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23274;
                    FStar_Syntax_Syntax.pos = uu____23275;
                    FStar_Syntax_Syntax.vars = uu____23276;_},
                  uu____23277),
                 uu____23278) ->
                  let uu____23315 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23315
              | (FStar_Syntax_Syntax.Tm_refine uu____23316, uu____23317) ->
                  let t21 =
                    let uu____23325 = base_and_refinement env t2 in
                    FStar_All.pipe_left force_refinement uu____23325 in
                  solve_t env
                    (let uu___3358_23351 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3358_23351.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3358_23351.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3358_23351.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3358_23351.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3358_23351.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3358_23351.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3358_23351.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3358_23351.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3358_23351.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23352, FStar_Syntax_Syntax.Tm_refine uu____23353) ->
                  let t11 =
                    let uu____23361 = base_and_refinement env t1 in
                    FStar_All.pipe_left force_refinement uu____23361 in
                  solve_t env
                    (let uu___3365_23387 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3365_23387.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3365_23387.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3365_23387.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3365_23387.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3365_23387.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3365_23387.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3365_23387.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3365_23387.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3365_23387.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match (s1, brs1),
                 FStar_Syntax_Syntax.Tm_match (s2, brs2)) ->
                  let by_smt uu____23469 =
                    let uu____23470 = guard_of_prob env wl problem t1 t2 in
                    match uu____23470 with
                    | (guard, wl1) ->
                        let uu____23477 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu____23477 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu____23696 = br1 in
                        (match uu____23696 with
                         | (p1, w1, uu____23725) ->
                             let uu____23742 = br2 in
                             (match uu____23742 with
                              | (p2, w2, uu____23765) ->
                                  let uu____23770 =
                                    let uu____23772 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu____23772 in
                                  if uu____23770
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23799 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu____23799 with
                                     | ((p11, w11, e1), s) ->
                                         let uu____23836 = br2 in
                                         (match uu____23836 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu____23869 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23869 in
                                              let uu____23874 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23905,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu____23926) ->
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
                                                    let uu____23985 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu____23985 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Util.bind_opt uu____23874
                                                (fun uu____24057 ->
                                                   match uu____24057 with
                                                   | (wprobs, wl2) ->
                                                       let uu____24094 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu____24094
                                                        with
                                                        | (prob, wl3) ->
                                                            ((let uu____24115
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu____24115
                                                              then
                                                                let uu____24120
                                                                  =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu____24122
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24120
                                                                  uu____24122
                                                              else ());
                                                             (let uu____24128
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Util.bind_opt
                                                                uu____24128
                                                                (fun
                                                                   uu____24164
                                                                   ->
                                                                   match uu____24164
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
                    | uu____24293 -> FStar_Pervasives_Native.None in
                  let uu____24334 = solve_branches wl brs1 brs2 in
                  (match uu____24334 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24360 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu____24360 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu____24387 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu____24387 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu____24421 =
                                FStar_List.map
                                  (fun uu____24433 ->
                                     match uu____24433 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu____24421 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu____24442 =
                              let uu____24443 =
                                let uu____24444 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1 in
                                attempt uu____24444
                                  (let uu___3464_24452 = wl3 in
                                   {
                                     attempting =
                                       (uu___3464_24452.attempting);
                                     wl_deferred =
                                       (uu___3464_24452.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3464_24452.wl_deferred_to_tac);
                                     ctr = (uu___3464_24452.ctr);
                                     defer_ok = (uu___3464_24452.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3464_24452.umax_heuristic_ok);
                                     tcenv = (uu___3464_24452.tcenv);
                                     wl_implicits =
                                       (uu___3464_24452.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3464_24452.repr_subcomp_allowed)
                                   }) in
                              solve env uu____24443 in
                            (match uu____24442 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24458 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24467 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu____24467 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24470, uu____24471) ->
                  let head1 =
                    let uu____24495 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24495
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24541 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24541
                      FStar_Pervasives_Native.fst in
                  ((let uu____24587 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24587
                    then
                      let uu____24591 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24593 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24595 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24591 uu____24593 uu____24595
                    else ());
                   (let no_free_uvars t =
                      (let uu____24609 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24609) &&
                        (let uu____24613 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24613) in
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
                      let uu____24632 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24632 = FStar_Syntax_Util.Equal in
                    let uu____24633 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24633
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24637 = equal t1 t2 in
                         (if uu____24637
                          then
                            let uu____24640 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24640
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24645 =
                            let uu____24652 = equal t1 t2 in
                            if uu____24652
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24665 = mk_eq2 wl env orig t1 t2 in
                               match uu____24665 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24645 with
                          | (guard, wl1) ->
                              let uu____24686 = solve_prob orig guard [] wl1 in
                              solve env uu____24686))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24689, uu____24690) ->
                  let head1 =
                    let uu____24698 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24698
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24744 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24744
                      FStar_Pervasives_Native.fst in
                  ((let uu____24790 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24790
                    then
                      let uu____24794 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24796 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24798 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24794 uu____24796 uu____24798
                    else ());
                   (let no_free_uvars t =
                      (let uu____24812 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24812) &&
                        (let uu____24816 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24816) in
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
                      let uu____24835 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24835 = FStar_Syntax_Util.Equal in
                    let uu____24836 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24836
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24840 = equal t1 t2 in
                         (if uu____24840
                          then
                            let uu____24843 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24843
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24848 =
                            let uu____24855 = equal t1 t2 in
                            if uu____24855
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24868 = mk_eq2 wl env orig t1 t2 in
                               match uu____24868 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24848 with
                          | (guard, wl1) ->
                              let uu____24889 = solve_prob orig guard [] wl1 in
                              solve env uu____24889))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24892, uu____24893) ->
                  let head1 =
                    let uu____24895 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24895
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24941 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24941
                      FStar_Pervasives_Native.fst in
                  ((let uu____24987 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24987
                    then
                      let uu____24991 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24993 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24995 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24991 uu____24993 uu____24995
                    else ());
                   (let no_free_uvars t =
                      (let uu____25009 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25009) &&
                        (let uu____25013 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25013) in
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
                      let uu____25032 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25032 = FStar_Syntax_Util.Equal in
                    let uu____25033 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25033
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25037 = equal t1 t2 in
                         (if uu____25037
                          then
                            let uu____25040 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25040
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25045 =
                            let uu____25052 = equal t1 t2 in
                            if uu____25052
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25065 = mk_eq2 wl env orig t1 t2 in
                               match uu____25065 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25045 with
                          | (guard, wl1) ->
                              let uu____25086 = solve_prob orig guard [] wl1 in
                              solve env uu____25086))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25089, uu____25090) ->
                  let head1 =
                    let uu____25092 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25092
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25138 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25138
                      FStar_Pervasives_Native.fst in
                  ((let uu____25184 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25184
                    then
                      let uu____25188 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25190 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25192 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25188 uu____25190 uu____25192
                    else ());
                   (let no_free_uvars t =
                      (let uu____25206 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25206) &&
                        (let uu____25210 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25210) in
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
                      let uu____25229 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25229 = FStar_Syntax_Util.Equal in
                    let uu____25230 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25230
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25234 = equal t1 t2 in
                         (if uu____25234
                          then
                            let uu____25237 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25237
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25242 =
                            let uu____25249 = equal t1 t2 in
                            if uu____25249
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25262 = mk_eq2 wl env orig t1 t2 in
                               match uu____25262 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25242 with
                          | (guard, wl1) ->
                              let uu____25283 = solve_prob orig guard [] wl1 in
                              solve env uu____25283))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25286, uu____25287) ->
                  let head1 =
                    let uu____25289 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25289
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25329 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25329
                      FStar_Pervasives_Native.fst in
                  ((let uu____25369 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25369
                    then
                      let uu____25373 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25375 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25377 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25373 uu____25375 uu____25377
                    else ());
                   (let no_free_uvars t =
                      (let uu____25391 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25391) &&
                        (let uu____25395 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25395) in
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
                      let uu____25414 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25414 = FStar_Syntax_Util.Equal in
                    let uu____25415 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25415
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25419 = equal t1 t2 in
                         (if uu____25419
                          then
                            let uu____25422 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25422
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25427 =
                            let uu____25434 = equal t1 t2 in
                            if uu____25434
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25447 = mk_eq2 wl env orig t1 t2 in
                               match uu____25447 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25427 with
                          | (guard, wl1) ->
                              let uu____25468 = solve_prob orig guard [] wl1 in
                              solve env uu____25468))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25471, uu____25472) ->
                  let head1 =
                    let uu____25490 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25490
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25530 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25530
                      FStar_Pervasives_Native.fst in
                  ((let uu____25570 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25570
                    then
                      let uu____25574 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25576 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25578 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25574 uu____25576 uu____25578
                    else ());
                   (let no_free_uvars t =
                      (let uu____25592 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25592) &&
                        (let uu____25596 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25596) in
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
                      let uu____25615 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25615 = FStar_Syntax_Util.Equal in
                    let uu____25616 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25616
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25620 = equal t1 t2 in
                         (if uu____25620
                          then
                            let uu____25623 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25623
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25628 =
                            let uu____25635 = equal t1 t2 in
                            if uu____25635
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25648 = mk_eq2 wl env orig t1 t2 in
                               match uu____25648 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25628 with
                          | (guard, wl1) ->
                              let uu____25669 = solve_prob orig guard [] wl1 in
                              solve env uu____25669))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25672, FStar_Syntax_Syntax.Tm_match uu____25673) ->
                  let head1 =
                    let uu____25697 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25697
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25737 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25737
                      FStar_Pervasives_Native.fst in
                  ((let uu____25777 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25777
                    then
                      let uu____25781 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25783 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25785 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25781 uu____25783 uu____25785
                    else ());
                   (let no_free_uvars t =
                      (let uu____25799 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25799) &&
                        (let uu____25803 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25803) in
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
                      let uu____25822 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25822 = FStar_Syntax_Util.Equal in
                    let uu____25823 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25823
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25827 = equal t1 t2 in
                         (if uu____25827
                          then
                            let uu____25830 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25830
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25835 =
                            let uu____25842 = equal t1 t2 in
                            if uu____25842
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25855 = mk_eq2 wl env orig t1 t2 in
                               match uu____25855 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25835 with
                          | (guard, wl1) ->
                              let uu____25876 = solve_prob orig guard [] wl1 in
                              solve env uu____25876))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25879, FStar_Syntax_Syntax.Tm_uinst uu____25880) ->
                  let head1 =
                    let uu____25888 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25888
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25928 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25928
                      FStar_Pervasives_Native.fst in
                  ((let uu____25968 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25968
                    then
                      let uu____25972 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25974 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25976 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25972 uu____25974 uu____25976
                    else ());
                   (let no_free_uvars t =
                      (let uu____25990 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25990) &&
                        (let uu____25994 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25994) in
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
                      let uu____26013 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26013 = FStar_Syntax_Util.Equal in
                    let uu____26014 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26014
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26018 = equal t1 t2 in
                         (if uu____26018
                          then
                            let uu____26021 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26021
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26026 =
                            let uu____26033 = equal t1 t2 in
                            if uu____26033
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26046 = mk_eq2 wl env orig t1 t2 in
                               match uu____26046 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26026 with
                          | (guard, wl1) ->
                              let uu____26067 = solve_prob orig guard [] wl1 in
                              solve env uu____26067))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26070, FStar_Syntax_Syntax.Tm_name uu____26071) ->
                  let head1 =
                    let uu____26073 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26073
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26113 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26113
                      FStar_Pervasives_Native.fst in
                  ((let uu____26153 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26153
                    then
                      let uu____26157 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26159 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26161 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26157 uu____26159 uu____26161
                    else ());
                   (let no_free_uvars t =
                      (let uu____26175 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26175) &&
                        (let uu____26179 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26179) in
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
                      let uu____26198 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26198 = FStar_Syntax_Util.Equal in
                    let uu____26199 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26199
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26203 = equal t1 t2 in
                         (if uu____26203
                          then
                            let uu____26206 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26206
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26211 =
                            let uu____26218 = equal t1 t2 in
                            if uu____26218
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26231 = mk_eq2 wl env orig t1 t2 in
                               match uu____26231 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26211 with
                          | (guard, wl1) ->
                              let uu____26252 = solve_prob orig guard [] wl1 in
                              solve env uu____26252))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26255, FStar_Syntax_Syntax.Tm_constant uu____26256) ->
                  let head1 =
                    let uu____26258 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26258
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26298 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26298
                      FStar_Pervasives_Native.fst in
                  ((let uu____26338 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26338
                    then
                      let uu____26342 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26344 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26346 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26342 uu____26344 uu____26346
                    else ());
                   (let no_free_uvars t =
                      (let uu____26360 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26360) &&
                        (let uu____26364 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26364) in
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
                      let uu____26383 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26383 = FStar_Syntax_Util.Equal in
                    let uu____26384 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26384
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26388 = equal t1 t2 in
                         (if uu____26388
                          then
                            let uu____26391 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26391
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26396 =
                            let uu____26403 = equal t1 t2 in
                            if uu____26403
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26416 = mk_eq2 wl env orig t1 t2 in
                               match uu____26416 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26396 with
                          | (guard, wl1) ->
                              let uu____26437 = solve_prob orig guard [] wl1 in
                              solve env uu____26437))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26440, FStar_Syntax_Syntax.Tm_fvar uu____26441) ->
                  let head1 =
                    let uu____26443 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26443
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26489 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26489
                      FStar_Pervasives_Native.fst in
                  ((let uu____26535 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26535
                    then
                      let uu____26539 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26541 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26543 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26539 uu____26541 uu____26543
                    else ());
                   (let no_free_uvars t =
                      (let uu____26557 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26557) &&
                        (let uu____26561 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26561) in
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
                      let uu____26580 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26580 = FStar_Syntax_Util.Equal in
                    let uu____26581 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26581
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26585 = equal t1 t2 in
                         (if uu____26585
                          then
                            let uu____26588 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26588
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26593 =
                            let uu____26600 = equal t1 t2 in
                            if uu____26600
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26613 = mk_eq2 wl env orig t1 t2 in
                               match uu____26613 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26593 with
                          | (guard, wl1) ->
                              let uu____26634 = solve_prob orig guard [] wl1 in
                              solve env uu____26634))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26637, FStar_Syntax_Syntax.Tm_app uu____26638) ->
                  let head1 =
                    let uu____26656 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26656
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26696 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26696
                      FStar_Pervasives_Native.fst in
                  ((let uu____26736 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26736
                    then
                      let uu____26740 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26742 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26744 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26740 uu____26742 uu____26744
                    else ());
                   (let no_free_uvars t =
                      (let uu____26758 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26758) &&
                        (let uu____26762 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26762) in
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
                      let uu____26781 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26781 = FStar_Syntax_Util.Equal in
                    let uu____26782 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26782
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26786 = equal t1 t2 in
                         (if uu____26786
                          then
                            let uu____26789 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26789
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26794 =
                            let uu____26801 = equal t1 t2 in
                            if uu____26801
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26814 = mk_eq2 wl env orig t1 t2 in
                               match uu____26814 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26794 with
                          | (guard, wl1) ->
                              let uu____26835 = solve_prob orig guard [] wl1 in
                              solve env uu____26835))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu____26838,
                 FStar_Syntax_Syntax.Tm_let uu____26839) ->
                  let uu____26866 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu____26866
                  then
                    let uu____26869 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu____26869
                  else
                    (let uu____26872 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu____26872 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26875, uu____26876) ->
                  let uu____26890 =
                    let uu____26896 =
                      let uu____26898 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____26900 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____26902 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____26904 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26898 uu____26900 uu____26902 uu____26904 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26896) in
                  FStar_Errors.raise_error uu____26890
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26908, FStar_Syntax_Syntax.Tm_let uu____26909) ->
                  let uu____26923 =
                    let uu____26929 =
                      let uu____26931 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____26933 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____26935 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____26937 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26931 uu____26933 uu____26935 uu____26937 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26929) in
                  FStar_Errors.raise_error uu____26923
                    t1.FStar_Syntax_Syntax.pos
              | uu____26941 ->
                  let uu____26946 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu____26946 orig))))
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
          (let uu____27012 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____27012
           then
             let uu____27017 =
               let uu____27019 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu____27019 in
             let uu____27020 =
               let uu____27022 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu____27022 in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27017 uu____27020
           else ());
          (let uu____27026 =
             let uu____27028 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu____27028 in
           if uu____27026
           then
             let uu____27031 =
               mklstr
                 (fun uu____27038 ->
                    let uu____27039 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu____27041 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27039 uu____27041) in
             giveup env uu____27031 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27063 =
                  mklstr
                    (fun uu____27070 ->
                       let uu____27071 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu____27073 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27071 uu____27073) in
                giveup env uu____27063 orig)
             else
               (let uu____27078 =
                  FStar_List.fold_left2
                    (fun uu____27099 ->
                       fun u1 ->
                         fun u2 ->
                           match uu____27099 with
                           | (univ_sub_probs, wl1) ->
                               let uu____27120 =
                                 let uu____27125 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange in
                                 let uu____27126 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange in
                                 sub_prob wl1 uu____27125
                                   FStar_TypeChecker_Common.EQ uu____27126
                                   "effect universes" in
                               (match uu____27120 with
                                | (p, wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu____27078 with
                | (univ_sub_probs, wl1) ->
                    let uu____27146 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu____27146 with
                     | (ret_sub_prob, wl2) ->
                         let uu____27154 =
                           FStar_List.fold_right2
                             (fun uu____27191 ->
                                fun uu____27192 ->
                                  fun uu____27193 ->
                                    match (uu____27191, uu____27192,
                                            uu____27193)
                                    with
                                    | ((a1, uu____27237), (a2, uu____27239),
                                       (arg_sub_probs, wl3)) ->
                                        let uu____27272 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu____27272 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu____27154 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu____27299 =
                                  let uu____27302 =
                                    let uu____27305 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd) in
                                    FStar_List.append arg_sub_probs
                                      uu____27305 in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27302 in
                                FStar_List.append univ_sub_probs uu____27299 in
                              let guard =
                                let guard =
                                  let uu____27327 =
                                    FStar_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu____27327 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f in
                              let wl4 =
                                let uu___3617_27336 = wl3 in
                                {
                                  attempting = (uu___3617_27336.attempting);
                                  wl_deferred = (uu___3617_27336.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3617_27336.wl_deferred_to_tac);
                                  ctr = (uu___3617_27336.ctr);
                                  defer_ok = (uu___3617_27336.defer_ok);
                                  smt_ok = (uu___3617_27336.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3617_27336.umax_heuristic_ok);
                                  tcenv = (uu___3617_27336.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3617_27336.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu____27338 = attempt sub_probs wl5 in
                              solve env uu____27338)))) in
        let solve_layered_sub c11 c21 =
          (let uu____27351 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu____27351
           then
             let uu____27356 =
               let uu____27358 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____27358
                 FStar_Syntax_Print.comp_to_string in
             let uu____27360 =
               let uu____27362 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____27362
                 FStar_Syntax_Print.comp_to_string in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27356 uu____27360
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let subcomp_name =
               let uu____27373 =
                 let uu____27375 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____27375 FStar_Ident.string_of_id in
               let uu____27377 =
                 let uu____27379 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____27379 FStar_Ident.string_of_id in
               FStar_Util.format2 "%s <: %s" uu____27373 uu____27377 in
             let lift_c1 edge =
               let uu____27396 =
                 let uu____27401 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                 FStar_All.pipe_right uu____27401
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env) in
               FStar_All.pipe_right uu____27396
                 (fun uu____27418 ->
                    match uu____27418 with
                    | (c, g) ->
                        let uu____27429 =
                          FStar_Syntax_Util.comp_to_comp_typ c in
                        (uu____27429, g)) in
             let uu____27430 =
               let uu____27442 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name in
               match uu____27442 with
               | FStar_Pervasives_Native.None ->
                   let uu____27456 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name in
                   (match uu____27456 with
                    | FStar_Pervasives_Native.None ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____27475 = lift_c1 edge in
                        (match uu____27475 with
                         | (c12, g_lift) ->
                             let uu____27493 =
                               let uu____27496 =
                                 let uu____27497 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env) in
                                 FStar_All.pipe_right uu____27497
                                   FStar_Syntax_Util.get_stronger_vc_combinator in
                               FStar_All.pipe_right uu____27496
                                 (fun ts ->
                                    let uu____27503 =
                                      let uu____27504 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs in
                                      FStar_All.pipe_right uu____27504
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____27503
                                      (fun uu____27515 ->
                                         FStar_Pervasives_Native.Some
                                           uu____27515)) in
                             (c12, g_lift, uu____27493, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____27521 =
                     let uu____27524 =
                       let uu____27525 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs in
                       FStar_All.pipe_right uu____27525
                         FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____27524
                       (fun uu____27536 ->
                          FStar_Pervasives_Native.Some uu____27536) in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____27521,
                     true) in
             match uu____27430 with
             | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____27552 =
                     mklstr
                       (fun uu____27559 ->
                          let uu____27560 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name in
                          let uu____27562 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____27560 uu____27562) in
                   giveup env uu____27552 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must in
                    let wl1 =
                      let uu___3652_27571 = wl in
                      {
                        attempting = (uu___3652_27571.attempting);
                        wl_deferred = (uu___3652_27571.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3652_27571.wl_deferred_to_tac);
                        ctr = (uu___3652_27571.ctr);
                        defer_ok = (uu___3652_27571.defer_ok);
                        smt_ok = (uu___3652_27571.smt_ok);
                        umax_heuristic_ok =
                          (uu___3652_27571.umax_heuristic_ok);
                        tcenv = (uu___3652_27571.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3652_27571.repr_subcomp_allowed)
                      } in
                    let uu____27572 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____27597 =
                             let uu____27598 = FStar_Syntax_Subst.compress t in
                             uu____27598.FStar_Syntax_Syntax.n in
                           match uu____27597 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____27602 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1, uu____27617)
                               -> is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1, uu____27623) ->
                               is_uvar t1
                           | uu____27648 -> false in
                         FStar_List.fold_right2
                           (fun uu____27682 ->
                              fun uu____27683 ->
                                fun uu____27684 ->
                                  match (uu____27682, uu____27683,
                                          uu____27684)
                                  with
                                  | ((a1, uu____27728), (a2, uu____27730),
                                     (is_sub_probs, wl2)) ->
                                      let uu____27763 = is_uvar a1 in
                                      if uu____27763
                                      then
                                        ((let uu____27773 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns") in
                                          if uu____27773
                                          then
                                            let uu____27778 =
                                              FStar_Syntax_Print.term_to_string
                                                a1 in
                                            let uu____27780 =
                                              FStar_Syntax_Print.term_to_string
                                                a2 in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____27778 uu____27780
                                          else ());
                                         (let uu____27785 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar" in
                                          match uu____27785 with
                                          | (p, wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                    match uu____27572 with
                    | (is_sub_probs, wl2) ->
                        let uu____27813 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type" in
                        (match uu____27813 with
                         | (ret_sub_prob, wl3) ->
                             let stronger_t_shape_error s =
                               let uu____27830 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name in
                               let uu____27832 =
                                 FStar_Syntax_Print.term_to_string stronger_t in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____27830 s uu____27832 in
                             let uu____27835 =
                               let uu____27864 =
                                 let uu____27865 =
                                   FStar_Syntax_Subst.compress stronger_t in
                                 uu____27865.FStar_Syntax_Syntax.n in
                               match uu____27864 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____27925 =
                                     FStar_Syntax_Subst.open_comp bs c in
                                   (match uu____27925 with
                                    | (bs', c3) ->
                                        let a = FStar_List.hd bs' in
                                        let bs1 = FStar_List.tail bs' in
                                        let uu____27988 =
                                          let uu____28007 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one)) in
                                          FStar_All.pipe_right uu____28007
                                            (fun uu____28111 ->
                                               match uu____28111 with
                                               | (l1, l2) ->
                                                   let uu____28184 =
                                                     FStar_List.hd l2 in
                                                   (l1, uu____28184)) in
                                        (match uu____27988 with
                                         | (rest_bs, f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____28289 ->
                                   let uu____28290 =
                                     let uu____28296 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders" in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____28296) in
                                   FStar_Errors.raise_error uu____28290 r in
                             (match uu____27835 with
                              | (a_b, rest_bs, f_b, stronger_c) ->
                                  let uu____28372 =
                                    let uu____28379 =
                                      let uu____28380 =
                                        let uu____28381 =
                                          let uu____28388 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst in
                                          (uu____28388,
                                            (c21.FStar_Syntax_Syntax.result_typ)) in
                                        FStar_Syntax_Syntax.NT uu____28381 in
                                      [uu____28380] in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____28379
                                      (fun b ->
                                         let uu____28404 =
                                           FStar_Syntax_Print.binder_to_string
                                             b in
                                         let uu____28406 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name in
                                         let uu____28408 =
                                           FStar_Range.string_of_range r in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____28404 uu____28406
                                           uu____28408) r in
                                  (match uu____28372 with
                                   | (rest_bs_uvars, g_uvars) ->
                                       let wl4 =
                                         let uu___3717_28418 = wl3 in
                                         {
                                           attempting =
                                             (uu___3717_28418.attempting);
                                           wl_deferred =
                                             (uu___3717_28418.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3717_28418.wl_deferred_to_tac);
                                           ctr = (uu___3717_28418.ctr);
                                           defer_ok =
                                             (uu___3717_28418.defer_ok);
                                           smt_ok = (uu___3717_28418.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3717_28418.umax_heuristic_ok);
                                           tcenv = (uu___3717_28418.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3717_28418.repr_subcomp_allowed)
                                         } in
                                       let substs =
                                         FStar_List.map2
                                           (fun b ->
                                              fun t ->
                                                let uu____28443 =
                                                  let uu____28450 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst in
                                                  (uu____28450, t) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____28443) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars) in
                                       let uu____28467 =
                                         let f_sort_is =
                                           let uu____28477 =
                                             let uu____28480 =
                                               let uu____28481 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____28481.FStar_Syntax_Syntax.sort in
                                             let uu____28490 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name in
                                             let uu____28492 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type" in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____28480 uu____28490 r
                                               uu____28492 in
                                           FStar_All.pipe_right uu____28477
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs)) in
                                         let uu____28499 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_List.fold_left2
                                           (fun uu____28535 ->
                                              fun f_sort_i ->
                                                fun c1_i ->
                                                  match uu____28535 with
                                                  | (ps, wl5) ->
                                                      ((let uu____28557 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns") in
                                                        if uu____28557
                                                        then
                                                          let uu____28562 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i in
                                                          let uu____28564 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____28562
                                                            uu____28564
                                                        else ());
                                                       (let uu____28569 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1" in
                                                        match uu____28569
                                                        with
                                                        | (p, wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____28499 in
                                       (match uu____28467 with
                                        | (f_sub_probs, wl5) ->
                                            let stronger_ct =
                                              let uu____28594 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs) in
                                              FStar_All.pipe_right
                                                uu____28594
                                                FStar_Syntax_Util.comp_to_comp_typ in
                                            let uu____28595 =
                                              let g_sort_is =
                                                let uu____28605 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name in
                                                let uu____28607 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr" in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____28605 r uu____28607 in
                                              let uu____28610 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst) in
                                              FStar_List.fold_left2
                                                (fun uu____28646 ->
                                                   fun g_sort_i ->
                                                     fun c2_i ->
                                                       match uu____28646 with
                                                       | (ps, wl6) ->
                                                           ((let uu____28668
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                             if uu____28668
                                                             then
                                                               let uu____28673
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i in
                                                               let uu____28675
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____28673
                                                                 uu____28675
                                                             else ());
                                                            (let uu____28680
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2" in
                                                             match uu____28680
                                                             with
                                                             | (p, wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____28610 in
                                            (match uu____28595 with
                                             | (g_sub_probs, wl6) ->
                                                 let fml =
                                                   let uu____28707 =
                                                     let uu____28712 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                     let uu____28713 =
                                                       let uu____28714 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                       FStar_Pervasives_Native.fst
                                                         uu____28714 in
                                                     (uu____28712,
                                                       uu____28713) in
                                                   match uu____28707 with
                                                   | (u, wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange in
                                                 let sub_probs =
                                                   let uu____28742 =
                                                     let uu____28745 =
                                                       let uu____28748 =
                                                         let uu____28751 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____28751 in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____28748 in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____28745 in
                                                   ret_sub_prob ::
                                                     uu____28742 in
                                                 let guard =
                                                   let guard =
                                                     let uu____28775 =
                                                       FStar_List.map p_guard
                                                         sub_probs in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____28775 in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                       -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f in
                                                 let wl7 =
                                                   let uu____28786 =
                                                     let uu____28789 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml in
                                                     FStar_All.pipe_left
                                                       (fun uu____28792 ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____28792)
                                                       uu____28789 in
                                                   solve_prob orig
                                                     uu____28786 [] wl6 in
                                                 let uu____28793 =
                                                   attempt sub_probs wl7 in
                                                 solve env uu____28793))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu____28821 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____28823 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu____28823]
               | x -> x in
             let c12 =
               let uu___3775_28826 = c11 in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3775_28826.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3775_28826.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3775_28826.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3775_28826.FStar_Syntax_Syntax.flags)
               } in
             let uu____28827 =
               let uu____28832 =
                 FStar_All.pipe_right
                   (let uu___3778_28834 = c12 in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3778_28834.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3778_28834.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3778_28834.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3778_28834.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____28832
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env) in
             FStar_All.pipe_right uu____28827
               (fun uu____28848 ->
                  match uu____28848 with
                  | (c, g) ->
                      let uu____28855 =
                        let uu____28857 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu____28857 in
                      if uu____28855
                      then
                        let uu____28860 =
                          let uu____28866 =
                            let uu____28868 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu____28870 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____28868 uu____28870 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____28866) in
                        FStar_Errors.raise_error uu____28860 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu____28876 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____28879 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name in
                 Prims.op_Negation uu____28879))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name) in
           if uu____28876
           then
             let uu____28882 =
               mklstr
                 (fun uu____28889 ->
                    let uu____28890 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____28892 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____28890 uu____28892) in
             giveup env uu____28882 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_28903 ->
                        match uu___29_28903 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu____28908 -> false)) in
              let uu____28910 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu____28940)::uu____28941,
                   (wp2, uu____28943)::uu____28944) -> (wp1, wp2)
                | uu____29017 ->
                    let uu____29042 =
                      let uu____29048 =
                        let uu____29050 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu____29052 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____29050 uu____29052 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____29048) in
                    FStar_Errors.raise_error uu____29042
                      env.FStar_TypeChecker_Env.range in
              match uu____28910 with
              | (wpc1, wpc2) ->
                  let uu____29062 = FStar_Util.physical_equality wpc1 wpc2 in
                  if uu____29062
                  then
                    let uu____29065 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu____29065 wl
                  else
                    (let uu____29069 =
                       let uu____29076 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.must uu____29076 in
                     match uu____29069 with
                     | (c2_decl, qualifiers) ->
                         let uu____29097 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu____29097
                         then
                           let c1_repr =
                             let uu____29104 =
                               let uu____29105 =
                                 let uu____29106 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu____29106 in
                               let uu____29107 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____29105 uu____29107 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____29104 in
                           let c2_repr =
                             let uu____29110 =
                               let uu____29111 =
                                 FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu____29112 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____29111 uu____29112 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____29110 in
                           let uu____29114 =
                             let uu____29119 =
                               let uu____29121 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu____29123 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____29121 uu____29123 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____29119 in
                           (match uu____29114 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu____29129 = attempt [prob] wl2 in
                                solve env uu____29129)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____29149 = lift_c1 () in
                                   FStar_All.pipe_right uu____29149
                                     (fun ct ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu____29172 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____29172
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu____29182 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu____29182 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu____29189 =
                                       let uu____29190 =
                                         let uu____29207 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu____29210 =
                                           let uu____29221 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu____29221; wpc1_2] in
                                         (uu____29207, uu____29210) in
                                       FStar_Syntax_Syntax.Tm_app uu____29190 in
                                     FStar_Syntax_Syntax.mk uu____29189 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu____29270 =
                                      let uu____29271 =
                                        let uu____29288 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu____29291 =
                                          let uu____29302 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____29311 =
                                            let uu____29322 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu____29322; wpc1_2] in
                                          uu____29302 :: uu____29311 in
                                        (uu____29288, uu____29291) in
                                      FStar_Syntax_Syntax.Tm_app uu____29271 in
                                    FStar_Syntax_Syntax.mk uu____29270 r)) in
                            (let uu____29376 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____29376
                             then
                               let uu____29381 =
                                 let uu____29383 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string
                                   uu____29383 in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____29381
                             else ());
                            (let uu____29387 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu____29387 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu____29396 =
                                     let uu____29399 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_All.pipe_left
                                       (fun uu____29402 ->
                                          FStar_Pervasives_Native.Some
                                            uu____29402) uu____29399 in
                                   solve_prob orig uu____29396 [] wl1 in
                                 let uu____29403 = attempt [base_prob] wl2 in
                                 solve env uu____29403))))) in
        let uu____29404 = FStar_Util.physical_equality c1 c2 in
        if uu____29404
        then
          let uu____29407 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____29407
        else
          ((let uu____29411 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____29411
            then
              let uu____29416 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____29418 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29416
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29418
            else ());
           (let uu____29423 =
              let uu____29432 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____29435 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____29432, uu____29435) in
            match uu____29423 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____29453),
                    FStar_Syntax_Syntax.Total (t2, uu____29455)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29472 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29472 wl
                 | (FStar_Syntax_Syntax.GTotal uu____29474,
                    FStar_Syntax_Syntax.Total uu____29475) ->
                     let uu____29492 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu____29492 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____29496),
                    FStar_Syntax_Syntax.Total (t2, uu____29498)) ->
                     let uu____29515 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29515 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____29518),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29520)) ->
                     let uu____29537 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29537 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____29540),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29542)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29559 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29559 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____29562),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29564)) ->
                     let uu____29581 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu____29581 orig
                 | (FStar_Syntax_Syntax.GTotal uu____29584,
                    FStar_Syntax_Syntax.Comp uu____29585) ->
                     let uu____29594 =
                       let uu___3902_29597 = problem in
                       let uu____29600 =
                         let uu____29601 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29601 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3902_29597.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29600;
                         FStar_TypeChecker_Common.relation =
                           (uu___3902_29597.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3902_29597.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3902_29597.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3902_29597.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3902_29597.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3902_29597.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3902_29597.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3902_29597.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29594 wl
                 | (FStar_Syntax_Syntax.Total uu____29602,
                    FStar_Syntax_Syntax.Comp uu____29603) ->
                     let uu____29612 =
                       let uu___3902_29615 = problem in
                       let uu____29618 =
                         let uu____29619 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29619 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3902_29615.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29618;
                         FStar_TypeChecker_Common.relation =
                           (uu___3902_29615.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3902_29615.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3902_29615.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3902_29615.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3902_29615.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3902_29615.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3902_29615.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3902_29615.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29612 wl
                 | (FStar_Syntax_Syntax.Comp uu____29620,
                    FStar_Syntax_Syntax.GTotal uu____29621) ->
                     let uu____29630 =
                       let uu___3914_29633 = problem in
                       let uu____29636 =
                         let uu____29637 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29637 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3914_29633.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3914_29633.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3914_29633.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29636;
                         FStar_TypeChecker_Common.element =
                           (uu___3914_29633.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3914_29633.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3914_29633.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3914_29633.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3914_29633.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3914_29633.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29630 wl
                 | (FStar_Syntax_Syntax.Comp uu____29638,
                    FStar_Syntax_Syntax.Total uu____29639) ->
                     let uu____29648 =
                       let uu___3914_29651 = problem in
                       let uu____29654 =
                         let uu____29655 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29655 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3914_29651.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3914_29651.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3914_29651.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29654;
                         FStar_TypeChecker_Common.element =
                           (uu___3914_29651.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3914_29651.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3914_29651.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3914_29651.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3914_29651.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3914_29651.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29648 wl
                 | (FStar_Syntax_Syntax.Comp uu____29656,
                    FStar_Syntax_Syntax.Comp uu____29657) ->
                     let uu____29658 =
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
                     if uu____29658
                     then
                       let uu____29661 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____29661 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29668 =
                            let uu____29673 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu____29673
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29682 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____29683 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____29682, uu____29683)) in
                          match uu____29668 with
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
                           (let uu____29691 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____29691
                            then
                              let uu____29696 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu____29698 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29696 uu____29698
                            else ());
                           (let uu____29703 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu____29703
                            then solve_layered_sub c12 c22
                            else
                              (let uu____29708 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu____29708 with
                               | FStar_Pervasives_Native.None ->
                                   let uu____29711 =
                                     mklstr
                                       (fun uu____29718 ->
                                          let uu____29719 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu____29721 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____29719 uu____29721) in
                                   giveup env uu____29711 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu____29732 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_All.pipe_right uu____29732 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____29782 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____29782 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____29807 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29838 ->
                match uu____29838 with
                | (u1, u2) ->
                    let uu____29846 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____29848 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____29846 uu____29848)) in
      FStar_All.pipe_right uu____29807 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial, [], (uu____29885, [])) when
          let uu____29912 = FStar_Options.print_implicits () in
          Prims.op_Negation uu____29912 -> "{}"
      | uu____29915 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29942 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu____29942
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu____29973 =
              FStar_List.map
                (fun uu____29987 ->
                   match uu____29987 with
                   | (msg, x) ->
                       let uu____29998 =
                         let uu____30000 = prob_to_string env x in
                         Prims.op_Hat ": " uu____30000 in
                       Prims.op_Hat msg uu____29998) defs in
            FStar_All.pipe_right uu____29973 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____30010 = carry g.FStar_TypeChecker_Common.deferred in
          let uu____30012 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu____30014 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30010 uu____30012 uu____30014 imps
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
                  let uu____30071 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu____30071
                  then
                    let uu____30079 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu____30081 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30079
                      (rel_to_string rel) uu____30081
                  else "TOP" in
                let uu____30087 =
                  new_problem wl env lhs rel rhs elt loc reason in
                match uu____30087 with
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
              let uu____30147 =
                let uu____30150 = FStar_TypeChecker_Env.get_range env in
                FStar_All.pipe_left
                  (fun uu____30153 ->
                     FStar_Pervasives_Native.Some uu____30153) uu____30150 in
              FStar_Syntax_Syntax.new_bv uu____30147 t1 in
            let uu____30154 =
              let uu____30159 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30159 in
            match uu____30154 with | (p, wl1) -> (p, x, wl1)
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
        (let uu____30231 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu____30231
         then
           let uu____30236 =
             FStar_Common.string_of_list
               (fun p -> FStar_Util.string_of_int (p_pid p)) probs.attempting in
           FStar_Util.print1 "solving problems %s {\n" uu____30236
         else ());
        (let uu____30243 =
           FStar_Util.record_time (fun uu____30250 -> solve env probs) in
         match uu____30243 with
         | (sol, ms) ->
             ((let uu____30264 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu____30264
               then
                 let uu____30269 = FStar_Util.string_of_int ms in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30269
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu____30285 =
                     FStar_Util.record_time
                       (fun uu____30292 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu____30285 with
                    | ((), ms1) ->
                        ((let uu____30305 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu____30305
                          then
                            let uu____30310 = FStar_Util.string_of_int ms1 in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30310
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu____30324 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu____30324
                     then
                       let uu____30331 = explain env d s in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30331
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
          ((let uu____30359 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____30359
            then
              let uu____30364 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30364
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu____30372 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____30372
             then
               let uu____30377 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30377
             else ());
            (let f2 =
               let uu____30383 =
                 let uu____30384 = FStar_Syntax_Util.unmeta f1 in
                 uu____30384.FStar_Syntax_Syntax.n in
               match uu____30383 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30388 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___4034_30389 = g in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4034_30389.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4034_30389.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4034_30389.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4034_30389.FStar_TypeChecker_Common.implicits)
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
            let uu____30441 =
              let uu____30442 =
                let uu____30443 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30444 ->
                       FStar_TypeChecker_Common.NonTrivial uu____30444) in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30443;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu____30442 in
            FStar_All.pipe_left
              (fun uu____30451 -> FStar_Pervasives_Native.Some uu____30451)
              uu____30441
let with_guard_no_simp :
  'uuuuuu30461 .
    'uuuuuu30461 ->
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
            let uu____30510 =
              let uu____30511 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30512 ->
                     FStar_TypeChecker_Common.NonTrivial uu____30512) in
              {
                FStar_TypeChecker_Common.guard_f = uu____30511;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              } in
            FStar_Pervasives_Native.Some uu____30510
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
          (let uu____30545 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____30545
           then
             let uu____30550 = FStar_Syntax_Print.term_to_string t1 in
             let uu____30552 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30550
               uu____30552
           else ());
          (let uu____30557 =
             let uu____30562 = FStar_TypeChecker_Env.get_range env in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30562 in
           match uu____30557 with
           | (prob, wl) ->
               let g =
                 let uu____30570 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30580 -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____30570 in
               ((let uu____30602 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____30602
                 then
                   let uu____30607 =
                     FStar_Common.string_of_option (guard_to_string env) g in
                   FStar_Util.print1 "} res = %s\n" uu____30607
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
        let uu____30628 = try_teq true env t1 t2 in
        match uu____30628 with
        | FStar_Pervasives_Native.None ->
            ((let uu____30633 = FStar_TypeChecker_Env.get_range env in
              let uu____30634 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____30633 uu____30634);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30642 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____30642
              then
                let uu____30647 = FStar_Syntax_Print.term_to_string t1 in
                let uu____30649 = FStar_Syntax_Print.term_to_string t2 in
                let uu____30651 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30647
                  uu____30649 uu____30651
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
        (let uu____30675 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____30675
         then
           let uu____30680 = FStar_Syntax_Print.term_to_string t1 in
           let uu____30682 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30680
             uu____30682
         else ());
        (let uu____30687 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu____30687 with
         | (prob, x, wl) ->
             let g =
               let uu____30702 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30713 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____30702 in
             ((let uu____30735 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____30735
               then
                 let uu____30740 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30740
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30748 =
                     let uu____30749 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu____30749 g1 in
                   FStar_Pervasives_Native.Some uu____30748)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____30771 = FStar_TypeChecker_Env.get_range env in
          let uu____30772 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____30771 uu____30772
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
        (let uu____30801 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____30801
         then
           let uu____30806 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____30808 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30806 uu____30808
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30819 =
           let uu____30826 = FStar_TypeChecker_Env.get_range env in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30826 "sub_comp" in
         match uu____30819 with
         | (prob, wl) ->
             let wl1 =
               let uu___4107_30837 = wl in
               {
                 attempting = (uu___4107_30837.attempting);
                 wl_deferred = (uu___4107_30837.wl_deferred);
                 wl_deferred_to_tac = (uu___4107_30837.wl_deferred_to_tac);
                 ctr = (uu___4107_30837.ctr);
                 defer_ok = (uu___4107_30837.defer_ok);
                 smt_ok = (uu___4107_30837.smt_ok);
                 umax_heuristic_ok = (uu___4107_30837.umax_heuristic_ok);
                 tcenv = (uu___4107_30837.tcenv);
                 wl_implicits = (uu___4107_30837.wl_implicits);
                 repr_subcomp_allowed = true
               } in
             let prob1 = FStar_TypeChecker_Common.CProb prob in
             (def_check_prob "sub_comp" prob1;
              (let uu____30842 =
                 FStar_Util.record_time
                   (fun uu____30854 ->
                      let uu____30855 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____30866 -> FStar_Pervasives_Native.None) in
                      FStar_All.pipe_left (with_guard env prob1) uu____30855) in
               match uu____30842 with
               | (r, ms) ->
                   ((let uu____30898 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench") in
                     if uu____30898
                     then
                       let uu____30903 = FStar_Syntax_Print.comp_to_string c1 in
                       let uu____30905 = FStar_Syntax_Print.comp_to_string c2 in
                       let uu____30907 = FStar_Util.string_of_int ms in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30903 uu____30905
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30907
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
      fun uu____30945 ->
        match uu____30945 with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____30988 =
                 let uu____30994 =
                   let uu____30996 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____30998 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____30996 uu____30998 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____30994) in
               let uu____31002 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____30988 uu____31002) in
            let equiv v v' =
              let uu____31015 =
                let uu____31020 = FStar_Syntax_Subst.compress_univ v in
                let uu____31021 = FStar_Syntax_Subst.compress_univ v' in
                (uu____31020, uu____31021) in
              match uu____31015 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31045 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v ->
                      let uu____31076 = FStar_Syntax_Subst.compress_univ v in
                      match uu____31076 with
                      | FStar_Syntax_Syntax.U_unif uu____31083 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31114 ->
                                    match uu____31114 with
                                    | (u, v') ->
                                        let uu____31123 = equiv v v' in
                                        if uu____31123
                                        then
                                          let uu____31128 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____31128 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____31149 -> [])) in
            let uu____31154 =
              let wl =
                let uu___4150_31158 = empty_worklist env in
                {
                  attempting = (uu___4150_31158.attempting);
                  wl_deferred = (uu___4150_31158.wl_deferred);
                  wl_deferred_to_tac = (uu___4150_31158.wl_deferred_to_tac);
                  ctr = (uu___4150_31158.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4150_31158.smt_ok);
                  umax_heuristic_ok = (uu___4150_31158.umax_heuristic_ok);
                  tcenv = (uu___4150_31158.tcenv);
                  wl_implicits = (uu___4150_31158.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4150_31158.repr_subcomp_allowed)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31177 ->
                      match uu____31177 with
                      | (lb, v) ->
                          let uu____31184 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu____31184 with
                           | USolved wl1 -> ()
                           | uu____31187 -> fail lb v))) in
            let rec check_ineq uu____31198 =
              match uu____31198 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu____31210) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____31238,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____31240,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____31253) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v1)))
                   | (uu____31261, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v2 -> check_ineq (u1, v2)))
                   | uu____31270 -> false) in
            let uu____31276 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31293 ->
                      match uu____31293 with
                      | (u, v) ->
                          let uu____31301 = check_ineq (u, v) in
                          if uu____31301
                          then true
                          else
                            ((let uu____31309 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____31309
                              then
                                let uu____31314 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____31316 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" uu____31314
                                  uu____31316
                              else ());
                             false))) in
            if uu____31276
            then ()
            else
              ((let uu____31326 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____31326
                then
                  ((let uu____31332 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31332);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31344 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31344))
                else ());
               (let uu____31357 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31357))
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
          let fail uu____31439 =
            match uu____31439 with
            | (d, s) ->
                let msg = explain env d s in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d) in
          let wl =
            let uu___4228_31466 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred in
            {
              attempting = (uu___4228_31466.attempting);
              wl_deferred = (uu___4228_31466.wl_deferred);
              wl_deferred_to_tac = (uu___4228_31466.wl_deferred_to_tac);
              ctr = (uu___4228_31466.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4228_31466.umax_heuristic_ok);
              tcenv = (uu___4228_31466.tcenv);
              wl_implicits = (uu___4228_31466.wl_implicits);
              repr_subcomp_allowed = (uu___4228_31466.repr_subcomp_allowed)
            } in
          (let uu____31469 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____31469
           then
             let uu____31474 = FStar_Util.string_of_bool defer_ok in
             let uu____31476 = wl_to_string wl in
             let uu____31478 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits) in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31474 uu____31476 uu____31478
           else ());
          (let g1 =
             let uu____31484 = solve_and_commit env wl fail in
             match uu____31484 with
             | FStar_Pervasives_Native.Some
                 (uu____31493::uu____31494, uu____31495, uu____31496) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred, defer_to_tac, imps) ->
                 let uu___4245_31530 = g in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4245_31530.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4245_31530.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31536 ->
                 failwith "Impossible: should have raised a failure already" in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1 in
            (let uu____31549 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook") in
             if uu____31549
             then
               let uu____31554 = guard_to_string env g2 in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____31554
             else ());
            (let uu___4253_31559 = g2 in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4253_31559.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4253_31559.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4253_31559.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4253_31559.FStar_TypeChecker_Common.implicits)
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
          (let uu____31655 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu____31655
           then
             let uu____31660 = guard_to_string env g in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31660
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g in
           let ret_g =
             let uu___4270_31667 = g1 in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4270_31667.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4270_31667.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4270_31667.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4270_31667.FStar_TypeChecker_Common.implicits)
             } in
           let uu____31668 =
             let uu____31670 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu____31670 in
           if uu____31668
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____31682 = FStar_TypeChecker_Env.get_range env in
                      let uu____31683 =
                        let uu____31685 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31685 in
                      FStar_Errors.diag uu____31682 uu____31683)
                   else ();
                   (let vc1 =
                      let uu____31691 =
                        let uu____31695 =
                          let uu____31697 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu____31697 in
                        FStar_Pervasives_Native.Some uu____31695 in
                      FStar_Profiling.profile
                        (fun uu____31700 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31691 "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu____31704 = FStar_TypeChecker_Env.get_range env in
                       let uu____31705 =
                         let uu____31707 =
                           FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31707 in
                       FStar_Errors.diag uu____31704 uu____31705)
                    else ();
                    (let uu____31713 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31713 "discharge_guard'" env vc1);
                    (let uu____31715 =
                       FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu____31715 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____31724 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____31725 =
                                 let uu____31727 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31727 in
                               FStar_Errors.diag uu____31724 uu____31725)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____31737 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____31738 =
                                 let uu____31740 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31740 in
                               FStar_Errors.diag uu____31737 uu____31738)
                            else ();
                            (let vcs =
                               let uu____31754 = FStar_Options.use_tactics () in
                               if uu____31754
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31776 ->
                                      (let uu____31778 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_All.pipe_left
                                         (fun uu____31780 -> ()) uu____31778);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31823 ->
                                               match uu____31823 with
                                               | (env1, goal, opts) ->
                                                   let uu____31839 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu____31839, opts)))))
                               else
                                 (let uu____31843 =
                                    let uu____31850 = FStar_Options.peek () in
                                    (env, vc2, uu____31850) in
                                  [uu____31843]) in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____31883 ->
                                     match uu____31883 with
                                     | (env1, goal, opts) ->
                                         let uu____31893 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu____31893 with
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
                                                 (let uu____31904 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____31905 =
                                                    let uu____31907 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu____31909 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____31907 uu____31909 in
                                                  FStar_Errors.diag
                                                    uu____31904 uu____31905)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____31916 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____31917 =
                                                    let uu____31919 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____31919 in
                                                  FStar_Errors.diag
                                                    uu____31916 uu____31917)
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
      let uu____31937 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____31937 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____31946 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31946
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____31960 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____31960 with
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
        let uu____31990 = try_teq false env t1 t2 in
        match uu____31990 with
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
             let uu____32045 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu____32045 with
             | (ctx_u, r) ->
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                 let uu____32055 =
                   let uu____32056 = FStar_Syntax_Subst.compress t_norm in
                   uu____32056.FStar_Syntax_Syntax.n in
                 (match uu____32055 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu____32062 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____32062
                        (fun uu____32065 ->
                           FStar_Pervasives_Native.Some uu____32065)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____32067) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu____32072 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____32072
                        (fun uu____32075 ->
                           FStar_Pervasives_Native.Some uu____32075)
                  | uu____32076 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_List.fold_left
               (fun b ->
                  fun imp ->
                    let uu____32089 =
                      let uu____32091 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_All.pipe_right uu____32091 FStar_Util.is_none in
                    if uu____32089
                    then
                      let uu____32099 = imp_value imp in
                      match uu____32099 with
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
        let uu____32128 =
          if is_tac
          then (false, true)
          else
            (((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
                (Prims.op_Negation env.FStar_TypeChecker_Env.lax)), false) in
        match uu____32128 with
        | (must_total, forcelax) ->
            let rec unresolved ctx_u =
              let uu____32164 =
                FStar_Syntax_Unionfind.find
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
              match uu____32164 with
              | FStar_Pervasives_Native.Some r ->
                  (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                   | FStar_Pervasives_Native.None -> false
                   | FStar_Pervasives_Native.Some uu____32171 ->
                       let uu____32172 =
                         let uu____32173 = FStar_Syntax_Subst.compress r in
                         uu____32173.FStar_Syntax_Syntax.n in
                       (match uu____32172 with
                        | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____32178)
                            -> unresolved ctx_u'
                        | uu____32195 -> false))
              | FStar_Pervasives_Native.None -> true in
            let rec until_fixpoint acc implicits =
              let uu____32219 = acc in
              match uu____32219 with
              | (out, changed) ->
                  (match implicits with
                   | [] ->
                       if Prims.op_Negation changed
                       then
                         let uu____32230 =
                           try_solve_single_valued_implicits env is_tac out in
                         (match uu____32230 with
                          | (out1, changed1) ->
                              if changed1
                              then until_fixpoint ([], false) out1
                              else out1)
                       else until_fixpoint ([], false) out
                   | hd::tl ->
                       let uu____32253 = hd in
                       (match uu____32253 with
                        | { FStar_TypeChecker_Common.imp_reason = reason;
                            FStar_TypeChecker_Common.imp_uvar = ctx_u;
                            FStar_TypeChecker_Common.imp_tm = tm;
                            FStar_TypeChecker_Common.imp_range = r;_} ->
                            if
                              ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                = FStar_Syntax_Syntax.Allow_unresolved
                            then until_fixpoint (out, true) tl
                            else
                              (let uu____32264 = unresolved ctx_u in
                               if uu____32264
                               then
                                 match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                     (env_dyn, tau)) ->
                                     let env1 = FStar_Dyn.undyn env_dyn in
                                     ((let uu____32275 =
                                         FStar_TypeChecker_Env.debug env1
                                           (FStar_Options.Other "Tac") in
                                       if uu____32275
                                       then
                                         let uu____32279 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             ctx_u in
                                         FStar_Util.print1
                                           "Running tactic for meta-arg %s\n"
                                           uu____32279
                                       else ());
                                      (let t =
                                         env1.FStar_TypeChecker_Env.synth_hook
                                           env1
                                           (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                           tau in
                                       let extra =
                                         let uu____32288 =
                                           teq_nosmt env1 t tm in
                                         match uu____32288 with
                                         | FStar_Pervasives_Native.None ->
                                             failwith
                                               "resolve_implicits: unifying with an unresolved uvar failed?"
                                         | FStar_Pervasives_Native.Some g1 ->
                                             g1.FStar_TypeChecker_Common.implicits in
                                       let ctx_u1 =
                                         let uu___4415_32298 = ctx_u in
                                         {
                                           FStar_Syntax_Syntax.ctx_uvar_head
                                             =
                                             (uu___4415_32298.FStar_Syntax_Syntax.ctx_uvar_head);
                                           FStar_Syntax_Syntax.ctx_uvar_gamma
                                             =
                                             (uu___4415_32298.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                           FStar_Syntax_Syntax.ctx_uvar_binders
                                             =
                                             (uu___4415_32298.FStar_Syntax_Syntax.ctx_uvar_binders);
                                           FStar_Syntax_Syntax.ctx_uvar_typ =
                                             (uu___4415_32298.FStar_Syntax_Syntax.ctx_uvar_typ);
                                           FStar_Syntax_Syntax.ctx_uvar_reason
                                             =
                                             (uu___4415_32298.FStar_Syntax_Syntax.ctx_uvar_reason);
                                           FStar_Syntax_Syntax.ctx_uvar_should_check
                                             =
                                             (uu___4415_32298.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                           FStar_Syntax_Syntax.ctx_uvar_range
                                             =
                                             (uu___4415_32298.FStar_Syntax_Syntax.ctx_uvar_range);
                                           FStar_Syntax_Syntax.ctx_uvar_meta
                                             = FStar_Pervasives_Native.None
                                         } in
                                       let hd1 =
                                         let uu___4418_32300 = hd in
                                         {
                                           FStar_TypeChecker_Common.imp_reason
                                             =
                                             (uu___4418_32300.FStar_TypeChecker_Common.imp_reason);
                                           FStar_TypeChecker_Common.imp_uvar
                                             = ctx_u1;
                                           FStar_TypeChecker_Common.imp_tm =
                                             (uu___4418_32300.FStar_TypeChecker_Common.imp_tm);
                                           FStar_TypeChecker_Common.imp_range
                                             =
                                             (uu___4418_32300.FStar_TypeChecker_Common.imp_range)
                                         } in
                                       until_fixpoint (out, true)
                                         (FStar_List.append extra tl)))
                                 | uu____32303 ->
                                     until_fixpoint ((hd :: out), changed) tl
                               else
                                 if
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                     = FStar_Syntax_Syntax.Allow_untyped
                                 then until_fixpoint (out, true) tl
                                 else
                                   (let env1 =
                                      let uu___4423_32315 = env in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4423_32315.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4423_32315.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4423_32315.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4423_32315.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4423_32315.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4423_32315.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4423_32315.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4423_32315.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4423_32315.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4423_32315.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4423_32315.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4423_32315.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4423_32315.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4423_32315.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4423_32315.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4423_32315.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4423_32315.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4423_32315.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4423_32315.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___4423_32315.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4423_32315.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4423_32315.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4423_32315.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4423_32315.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4423_32315.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4423_32315.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4423_32315.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4423_32315.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4423_32315.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4423_32315.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4423_32315.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4423_32315.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4423_32315.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4423_32315.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4423_32315.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4423_32315.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4423_32315.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4423_32315.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4423_32315.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4423_32315.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4423_32315.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4423_32315.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4423_32315.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4423_32315.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4423_32315.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4423_32315.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    let tm1 =
                                      norm_with_steps
                                        "FStar.TypeChecker.Rel.norm_with_steps.8"
                                        [FStar_TypeChecker_Env.Beta] env1 tm in
                                    let env2 =
                                      if forcelax
                                      then
                                        let uu___4428_32320 = env1 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___4428_32320.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___4428_32320.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___4428_32320.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___4428_32320.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___4428_32320.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___4428_32320.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___4428_32320.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___4428_32320.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___4428_32320.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___4428_32320.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___4428_32320.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___4428_32320.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___4428_32320.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___4428_32320.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___4428_32320.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___4428_32320.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___4428_32320.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___4428_32320.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___4428_32320.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___4428_32320.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___4428_32320.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___4428_32320.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___4428_32320.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___4428_32320.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___4428_32320.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___4428_32320.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___4428_32320.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___4428_32320.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___4428_32320.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___4428_32320.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___4428_32320.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (uu___4428_32320.FStar_TypeChecker_Env.enable_defer_to_tac)
                                        }
                                      else env1 in
                                    (let uu____32325 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env2)
                                         (FStar_Options.Other "Rel") in
                                     if uu____32325
                                     then
                                       let uu____32330 =
                                         FStar_Syntax_Print.uvar_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                       let uu____32332 =
                                         FStar_Syntax_Print.term_to_string
                                           tm1 in
                                       let uu____32334 =
                                         FStar_Syntax_Print.term_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                       let uu____32336 =
                                         FStar_Range.string_of_range r in
                                       FStar_Util.print5
                                         "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                         uu____32330 uu____32332 uu____32334
                                         reason uu____32336
                                     else ());
                                    (let g1 =
                                       try
                                         (fun uu___4434_32343 ->
                                            match () with
                                            | () ->
                                                env2.FStar_TypeChecker_Env.check_type_of
                                                  must_total env2 tm1
                                                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                           ()
                                       with
                                       | e when FStar_Errors.handleable e ->
                                           ((let uu____32350 =
                                               let uu____32360 =
                                                 let uu____32368 =
                                                   let uu____32370 =
                                                     FStar_Syntax_Print.uvar_to_string
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu____32372 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2 tm1 in
                                                   let uu____32374 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                   FStar_Util.format3
                                                     "Failed while checking implicit %s set to %s of expected type %s"
                                                     uu____32370 uu____32372
                                                     uu____32374 in
                                                 (FStar_Errors.Error_BadImplicit,
                                                   uu____32368, r) in
                                               [uu____32360] in
                                             FStar_Errors.add_errors
                                               uu____32350);
                                            FStar_Exn.raise e) in
                                     let g' =
                                       let uu____32393 =
                                         discharge_guard'
                                           (FStar_Pervasives_Native.Some
                                              (fun uu____32404 ->
                                                 let uu____32405 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm1 in
                                                 let uu____32407 =
                                                   FStar_Range.string_of_range
                                                     r in
                                                 let uu____32409 =
                                                   FStar_Range.string_of_range
                                                     tm1.FStar_Syntax_Syntax.pos in
                                                 FStar_Util.format4
                                                   "%s (Introduced at %s for %s resolved at %s)"
                                                   uu____32405 uu____32407
                                                   reason uu____32409)) env2
                                           g1 true in
                                       match uu____32393 with
                                       | FStar_Pervasives_Native.Some g2 ->
                                           g2
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                                     until_fixpoint
                                       ((FStar_List.append
                                           g'.FStar_TypeChecker_Common.implicits
                                           out), true) tl))))) in
            let uu___4446_32417 = g in
            let uu____32418 =
              until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4446_32417.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4446_32417.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4446_32417.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4446_32417.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = uu____32418
            }
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu____32433 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____32433
       then
         let uu____32438 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32438
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
      (let uu____32468 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____32468
       then
         let uu____32473 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32473
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____32480 = discharge_guard env g2 in
           FStar_All.pipe_left (fun uu____32481 -> ()) uu____32480
       | imp::uu____32483 ->
           let uu____32486 =
             let uu____32492 =
               let uu____32494 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____32496 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____32494 uu____32496
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32492) in
           FStar_Errors.raise_error uu____32486
             imp.FStar_TypeChecker_Common.imp_range)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32516 = teq env t1 t2 in
        force_trivial_guard env uu____32516
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32535 = teq_nosmt env t1 t2 in
        match uu____32535 with
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
          (let uu____32571 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu____32571
           then
             let uu____32576 =
               let uu____32578 =
                 FStar_All.pipe_right reason FStar_Util.is_none in
               if uu____32578
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must in
             let uu____32595 = FStar_Syntax_Print.term_to_string t1 in
             let uu____32597 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____32576
               uu____32595 uu____32597
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___4484_32613 = FStar_TypeChecker_Common.trivial_guard in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4484_32613.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4484_32613.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4484_32613.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4484_32613.FStar_TypeChecker_Common.implicits)
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
        (let uu____32649 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____32649
         then
           let uu____32654 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____32656 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32654
             uu____32656
         else ());
        (let uu____32661 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____32661 with
         | (prob, x, wl) ->
             let g =
               let uu____32680 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32691 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____32680 in
             ((let uu____32713 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____32713
               then
                 let uu____32718 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____32720 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____32722 =
                   let uu____32724 = FStar_Util.must g in
                   guard_to_string env uu____32724 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32718 uu____32720 uu____32722
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
        let uu____32761 = check_subtyping env t1 t2 in
        match uu____32761 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____32780 =
              let uu____32781 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu____32781 g in
            FStar_Pervasives_Native.Some uu____32780
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32800 = check_subtyping env t1 t2 in
        match uu____32800 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____32819 =
              let uu____32820 =
                let uu____32821 = FStar_Syntax_Syntax.mk_binder x in
                [uu____32821] in
              FStar_TypeChecker_Env.close_guard env uu____32820 g in
            FStar_Pervasives_Native.Some uu____32819
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____32859 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____32859
         then
           let uu____32864 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____32866 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32864
             uu____32866
         else ());
        (let uu____32871 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____32871 with
         | (prob, x, wl) ->
             let g =
               let uu____32886 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32897 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____32886 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32922 =
                      let uu____32923 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____32923] in
                    FStar_TypeChecker_Env.close_guard env uu____32922 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32964 = subtype_nosmt env t1 t2 in
        match uu____32964 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)