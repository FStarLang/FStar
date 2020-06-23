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
      (fun uu____780 ->
         match uu____780 with
         | (uu____796, m, p) ->
             let uu____807 = FStar_Thunk.force m in (uu____807, p)) wl_def
let (as_wl_deferred :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun wl ->
    fun d ->
      FStar_List.map
        (fun uu____859 ->
           match uu____859 with
           | (m, p) ->
               let uu____879 = FStar_Thunk.mkv m in ((wl.ctr), uu____879, p))
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
                    let uu____972 = FStar_Syntax_Unionfind.fresh r in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____972;
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
                   (let uu____1006 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace") in
                    if uu____1006
                    then
                      let uu____1010 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____1010
                    else ());
                   (ctx_uvar, t,
                     ((let uu___94_1016 = wl in
                       {
                         attempting = (uu___94_1016.attempting);
                         wl_deferred = (uu___94_1016.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___94_1016.wl_deferred_to_tac);
                         ctr = (uu___94_1016.ctr);
                         defer_ok = (uu___94_1016.defer_ok);
                         smt_ok = (uu___94_1016.smt_ok);
                         umax_heuristic_ok = (uu___94_1016.umax_heuristic_ok);
                         tcenv = (uu___94_1016.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits));
                         repr_subcomp_allowed =
                           (uu___94_1016.repr_subcomp_allowed)
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
            let uu___100_1049 = wl.tcenv in
            {
              FStar_TypeChecker_Env.solver =
                (uu___100_1049.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___100_1049.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___100_1049.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___100_1049.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___100_1049.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___100_1049.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___100_1049.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___100_1049.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___100_1049.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___100_1049.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___100_1049.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___100_1049.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___100_1049.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___100_1049.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___100_1049.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___100_1049.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___100_1049.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___100_1049.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___100_1049.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___100_1049.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___100_1049.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___100_1049.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___100_1049.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___100_1049.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___100_1049.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___100_1049.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___100_1049.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___100_1049.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___100_1049.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___100_1049.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___100_1049.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___100_1049.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___100_1049.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___100_1049.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___100_1049.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___100_1049.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___100_1049.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___100_1049.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___100_1049.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___100_1049.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___100_1049.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___100_1049.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___100_1049.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___100_1049.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___100_1049.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___100_1049.FStar_TypeChecker_Env.enable_defer_to_tac)
            } in
          let env1 = FStar_TypeChecker_Env.push_binders env bs in
          let uu____1051 = FStar_TypeChecker_Env.all_binders env1 in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____1051 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee ->
    match projectee with | Success _0 -> true | uu____1142 -> false
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred *
      FStar_TypeChecker_Common.implicits))
  = fun projectee -> match projectee with | Success _0 -> _0
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee ->
    match projectee with | Failed _0 -> true | uu____1183 -> false
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
        let uu___109_1220 = wl in
        let uu____1221 =
          let uu____1231 = as_wl_deferred wl defer_to_tac in
          FStar_List.append wl.wl_deferred_to_tac uu____1231 in
        {
          attempting = (uu___109_1220.attempting);
          wl_deferred = (uu___109_1220.wl_deferred);
          wl_deferred_to_tac = uu____1221;
          ctr = (uu___109_1220.ctr);
          defer_ok = (uu___109_1220.defer_ok);
          smt_ok = (uu___109_1220.smt_ok);
          umax_heuristic_ok = (uu___109_1220.umax_heuristic_ok);
          tcenv = (uu___109_1220.tcenv);
          wl_implicits = (FStar_List.append wl.wl_implicits imps);
          repr_subcomp_allowed = (uu___109_1220.repr_subcomp_allowed)
        }
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | COVARIANT -> true | uu____1257 -> false
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | CONTRAVARIANT -> true | uu____1268 -> false
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee ->
    match projectee with | INVARIANT -> true | uu____1279 -> false
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_1297 ->
    match uu___0_1297 with
    | FStar_TypeChecker_Common.EQ -> "="
    | FStar_TypeChecker_Common.SUB -> "<:"
    | FStar_TypeChecker_Common.SUBINV -> ":>"
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    let uu____1309 = FStar_Syntax_Util.head_and_args t in
    match uu____1309 with
    | (head, args) ->
        (match head.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
             let uu____1372 = FStar_Syntax_Print.ctx_uvar_to_string u in
             let uu____1374 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1389 =
                     let uu____1391 = FStar_List.hd s1 in
                     FStar_Syntax_Print.subst_to_string uu____1391 in
                   FStar_Util.format1 "@<%s>" uu____1389 in
             let uu____1395 = FStar_Syntax_Print.args_to_string args in
             FStar_Util.format3 "%s%s %s" uu____1372 uu____1374 uu____1395
         | uu____1398 -> FStar_Syntax_Print.term_to_string t)
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env ->
    fun uu___1_1410 ->
      match uu___1_1410 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1415 =
            let uu____1419 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
            let uu____1421 =
              let uu____1425 = term_to_string p.FStar_TypeChecker_Common.lhs in
              let uu____1427 =
                let uu____1431 =
                  let uu____1435 =
                    term_to_string p.FStar_TypeChecker_Common.rhs in
                  [uu____1435] in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1431 in
              uu____1425 :: uu____1427 in
            uu____1419 :: uu____1421 in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1415
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1446 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid in
          let uu____1448 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs in
          let uu____1450 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1446 uu____1448
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1450
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env ->
    fun uu___2_1464 ->
      match uu___2_1464 with
      | UNIV (u, t) ->
          let x =
            let uu____1470 = FStar_Options.hide_uvar_nums () in
            if uu____1470
            then "?"
            else
              (let uu____1477 = FStar_Syntax_Unionfind.univ_uvar_id u in
               FStar_All.pipe_right uu____1477 FStar_Util.string_of_int) in
          let uu____1481 = FStar_Syntax_Print.univ_to_string t in
          FStar_Util.format2 "UNIV %s <- %s" x uu____1481
      | TERM (u, t) ->
          let x =
            let uu____1488 = FStar_Options.hide_uvar_nums () in
            if uu____1488
            then "?"
            else
              (let uu____1495 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head in
               FStar_All.pipe_right uu____1495 FStar_Util.string_of_int) in
          let uu____1499 = FStar_TypeChecker_Normalize.term_to_string env t in
          FStar_Util.format2 "TERM %s <- %s" x uu____1499
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env -> fun uvis -> FStar_Common.string_of_list (uvi_to_string env) uvis
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms ->
    let uu____1529 =
      let uu____1533 = FStar_Util.set_elements nms in
      FStar_All.pipe_right uu____1533
        (FStar_List.map FStar_Syntax_Print.bv_to_string) in
    FStar_All.pipe_right uu____1529 (FStar_String.concat ", ")
let args_to_string :
  'uuuuuu1552 .
    (FStar_Syntax_Syntax.term * 'uuuuuu1552) Prims.list -> Prims.string
  =
  fun args ->
    let uu____1571 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1592 ->
              match uu____1592 with
              | (x, uu____1599) -> FStar_Syntax_Print.term_to_string x)) in
    FStar_All.pipe_right uu____1571 (FStar_String.concat " ")
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
        (let uu____1647 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____1647
         then
           let uu____1652 = FStar_Thunk.force reason in
           let uu____1655 = prob_to_string env prob in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1652 uu____1655
         else ());
        Failed (prob, reason)
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env ->
    fun reason ->
      fun prob ->
        let uu____1678 = mklstr (fun uu____1681 -> reason) in
        giveup env uu____1678 prob
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1687 ->
    match uu___3_1687 with
    | FStar_TypeChecker_Common.EQ -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV -> FStar_TypeChecker_Common.SUB
let invert :
  'uuuuuu1693 .
    'uuuuuu1693 FStar_TypeChecker_Common.problem ->
      'uuuuuu1693 FStar_TypeChecker_Common.problem
  =
  fun p ->
    let uu___169_1705 = p in
    {
      FStar_TypeChecker_Common.pid =
        (uu___169_1705.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___169_1705.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___169_1705.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___169_1705.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___169_1705.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___169_1705.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___169_1705.FStar_TypeChecker_Common.rank)
    }
let maybe_invert :
  'uuuuuu1713 .
    'uuuuuu1713 FStar_TypeChecker_Common.problem ->
      'uuuuuu1713 FStar_TypeChecker_Common.problem
  =
  fun p ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1733 ->
    match uu___4_1733 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1739 -> FStar_TypeChecker_Common.TProb uu____1739)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1745 -> FStar_TypeChecker_Common.CProb uu____1745)
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1751 ->
    match uu___5_1751 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___181_1757 = p in
           {
             FStar_TypeChecker_Common.pid =
               (uu___181_1757.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___181_1757.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___181_1757.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___181_1757.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___181_1757.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___181_1757.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___181_1757.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___181_1757.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___181_1757.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___185_1765 = p in
           {
             FStar_TypeChecker_Common.pid =
               (uu___185_1765.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___185_1765.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___185_1765.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___185_1765.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___185_1765.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___185_1765.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___185_1765.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___185_1765.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___185_1765.FStar_TypeChecker_Common.rank)
           })
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel ->
    fun uu___6_1778 ->
      match uu___6_1778 with
      | INVARIANT -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT -> invert_rel rel
      | COVARIANT -> rel
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1785 ->
    match uu___7_1785 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1798 ->
    match uu___8_1798 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1813 ->
    match uu___9_1813 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1828 ->
    match uu___10_1828 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1842 ->
    match uu___11_1842 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1856 ->
    match uu___12_1856 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1868 ->
    match uu___13_1868 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
let def_scope_wf :
  'uuuuuu1884 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu1884) Prims.list -> unit
  =
  fun msg ->
    fun rng ->
      fun r ->
        let uu____1914 =
          let uu____1916 = FStar_Options.defensive () in
          Prims.op_Negation uu____1916 in
        if uu____1914
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv, uu____1953)::bs ->
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
          let uu____2000 =
            match p_element prob with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____2024 = FStar_Syntax_Syntax.mk_binder x in
                [uu____2024] in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____2000
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2052 =
            match p_element prob with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____2076 = FStar_Syntax_Syntax.mk_binder x in
                [uu____2076] in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____2052 in
    def_scope_wf "p_scope" (p_loc prob) r; r
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg ->
    fun prob ->
      fun phi ->
        let uu____2123 =
          let uu____2125 = FStar_Options.defensive () in
          Prims.op_Negation uu____2125 in
        if uu____2123
        then ()
        else
          (let uu____2130 =
             let uu____2133 = p_scope prob in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____2133 in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____2130 phi)
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg ->
    fun prob ->
      fun comp ->
        let uu____2182 =
          let uu____2184 = FStar_Options.defensive () in
          Prims.op_Negation uu____2184 in
        if uu____2182
        then ()
        else
          (let uu____2189 = FStar_Syntax_Util.arrow [] comp in
           def_check_scoped msg prob uu____2189)
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg ->
    fun prob ->
      let uu____2209 =
        let uu____2211 = FStar_Options.defensive () in
        Prims.op_Negation uu____2211 in
      if uu____2209
      then ()
      else
        (let msgf m =
           let uu____2225 =
             let uu____2227 =
               let uu____2229 = FStar_Util.string_of_int (p_pid prob) in
               Prims.op_Hat uu____2229 (Prims.op_Hat "." m) in
             Prims.op_Hat "." uu____2227 in
           Prims.op_Hat msg uu____2225 in
         (let uu____2234 = msgf "scope" in
          let uu____2237 = p_scope prob in
          def_scope_wf uu____2234 (p_loc prob) uu____2237);
         (let uu____2249 = msgf "guard" in
          def_check_scoped uu____2249 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____2256 = msgf "lhs" in
                def_check_scoped uu____2256 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2259 = msgf "rhs" in
                def_check_scoped uu____2259 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____2266 = msgf "lhs" in
                def_check_scoped_comp uu____2266 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2269 = msgf "rhs" in
                def_check_scoped_comp uu____2269 prob
                  p.FStar_TypeChecker_Common.rhs))))
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl ->
    fun prob ->
      fun smt_ok ->
        let uu___278_2290 = wl in
        {
          attempting = [prob];
          wl_deferred = (uu___278_2290.wl_deferred);
          wl_deferred_to_tac = (uu___278_2290.wl_deferred_to_tac);
          ctr = (uu___278_2290.ctr);
          defer_ok = (uu___278_2290.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___278_2290.umax_heuristic_ok);
          tcenv = (uu___278_2290.tcenv);
          wl_implicits = (uu___278_2290.wl_implicits);
          repr_subcomp_allowed = (uu___278_2290.repr_subcomp_allowed)
        }
let wl_of_guard :
  'uuuuuu2298 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu2298 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env ->
    fun g ->
      let uu___282_2321 = empty_worklist env in
      let uu____2322 = FStar_List.map FStar_Pervasives_Native.snd g in
      {
        attempting = uu____2322;
        wl_deferred = (uu___282_2321.wl_deferred);
        wl_deferred_to_tac = (uu___282_2321.wl_deferred_to_tac);
        ctr = (uu___282_2321.ctr);
        defer_ok = (uu___282_2321.defer_ok);
        smt_ok = (uu___282_2321.smt_ok);
        umax_heuristic_ok = (uu___282_2321.umax_heuristic_ok);
        tcenv = (uu___282_2321.tcenv);
        wl_implicits = (uu___282_2321.wl_implicits);
        repr_subcomp_allowed = (uu___282_2321.repr_subcomp_allowed)
      }
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason ->
    fun prob ->
      fun wl ->
        let uu___287_2343 = wl in
        {
          attempting = (uu___287_2343.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          wl_deferred_to_tac = (uu___287_2343.wl_deferred_to_tac);
          ctr = (uu___287_2343.ctr);
          defer_ok = (uu___287_2343.defer_ok);
          smt_ok = (uu___287_2343.smt_ok);
          umax_heuristic_ok = (uu___287_2343.umax_heuristic_ok);
          tcenv = (uu___287_2343.tcenv);
          wl_implicits = (uu___287_2343.wl_implicits);
          repr_subcomp_allowed = (uu___287_2343.repr_subcomp_allowed)
        }
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason ->
    fun prob ->
      fun wl ->
        let uu____2370 = FStar_Thunk.mkv reason in defer uu____2370 prob wl
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs ->
    fun wl ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___295_2389 = wl in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___295_2389.wl_deferred);
         wl_deferred_to_tac = (uu___295_2389.wl_deferred_to_tac);
         ctr = (uu___295_2389.ctr);
         defer_ok = (uu___295_2389.defer_ok);
         smt_ok = (uu___295_2389.smt_ok);
         umax_heuristic_ok = (uu___295_2389.umax_heuristic_ok);
         tcenv = (uu___295_2389.tcenv);
         wl_implicits = (uu___295_2389.wl_implicits);
         repr_subcomp_allowed = (uu___295_2389.repr_subcomp_allowed)
       })
let mk_eq2 :
  'uuuuuu2403 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2403 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl ->
    fun env ->
      fun prob ->
        fun t1 ->
          fun t2 ->
            let uu____2437 = FStar_Syntax_Util.type_u () in
            match uu____2437 with
            | (t_type, u) ->
                let binders = FStar_TypeChecker_Env.all_binders env in
                let uu____2449 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None in
                (match uu____2449 with
                 | (uu____2461, tt, wl1) ->
                     let uu____2464 = FStar_Syntax_Util.mk_eq2 u tt t1 t2 in
                     (uu____2464, wl1))
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2470 ->
    match uu___14_2470 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun uu____2476 -> FStar_TypeChecker_Common.TProb uu____2476)
          (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun uu____2482 -> FStar_TypeChecker_Common.CProb uu____2482)
          (invert p)
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p ->
    let uu____2490 = FStar_All.pipe_right (p_reason p) FStar_List.length in
    uu____2490 = Prims.int_one
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero in
  fun uu____2510 -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr
let mk_problem :
  'uuuuuu2552 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'uuuuuu2552 ->
            FStar_TypeChecker_Common.rel ->
              'uuuuuu2552 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuuu2552 FStar_TypeChecker_Common.problem * worklist)
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
                        let uu____2639 =
                          let uu____2648 = FStar_Syntax_Syntax.mk_binder x in
                          [uu____2648] in
                        FStar_List.append scope uu____2639 in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1 in
                  let gamma =
                    let uu____2691 =
                      let uu____2694 =
                        FStar_List.map
                          (fun b ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1 in
                      FStar_List.rev uu____2694 in
                    FStar_List.append uu____2691
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma in
                  let uu____2713 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None in
                  match uu____2713 with
                  | (ctx_uvar, lg, wl1) ->
                      let prob =
                        let uu____2733 = next_pid () in
                        {
                          FStar_TypeChecker_Common.pid = uu____2733;
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
                  (let uu____2807 =
                     mk_problem wl scope orig lhs rel rhs elt reason in
                   match uu____2807 with
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
                  (let uu____2895 =
                     mk_problem wl scope orig lhs rel rhs elt reason in
                   match uu____2895 with
                   | (p, wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
let new_problem :
  'uuuuuu2933 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2933 ->
          FStar_TypeChecker_Common.rel ->
            'uuuuuu2933 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('uuuuuu2933 FStar_TypeChecker_Common.problem * worklist)
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
                          let uu____3001 = FStar_Syntax_Syntax.mk_binder x in
                          [uu____3001] in
                        let uu____3020 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0 in
                        FStar_Syntax_Util.arrow bs uu____3020 in
                  let uu____3023 =
                    let uu____3030 = FStar_TypeChecker_Env.all_binders env in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___378_3041 = wl in
                       {
                         attempting = (uu___378_3041.attempting);
                         wl_deferred = (uu___378_3041.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___378_3041.wl_deferred_to_tac);
                         ctr = (uu___378_3041.ctr);
                         defer_ok = (uu___378_3041.defer_ok);
                         smt_ok = (uu___378_3041.smt_ok);
                         umax_heuristic_ok =
                           (uu___378_3041.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___378_3041.wl_implicits);
                         repr_subcomp_allowed =
                           (uu___378_3041.repr_subcomp_allowed)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____3030
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None in
                  match uu____3023 with
                  | (ctx_uvar, lg, wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____3053 =
                              let uu____3054 =
                                let uu____3063 =
                                  FStar_Syntax_Syntax.bv_to_name x in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.as_arg uu____3063 in
                              [uu____3054] in
                            FStar_Syntax_Syntax.mk_Tm_app lg uu____3053 loc in
                      let prob =
                        let uu____3091 = next_pid () in
                        {
                          FStar_TypeChecker_Common.pid = uu____3091;
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
                let uu____3139 = next_pid () in
                {
                  FStar_TypeChecker_Common.pid = uu____3139;
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
  'uuuuuu3154 .
    worklist ->
      'uuuuuu3154 FStar_TypeChecker_Common.problem ->
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
              let uu____3187 =
                let uu____3190 =
                  let uu____3191 =
                    let uu____3198 = FStar_Syntax_Syntax.bv_to_name e in
                    (x, uu____3198) in
                  FStar_Syntax_Syntax.NT uu____3191 in
                [uu____3190] in
              FStar_Syntax_Subst.subst uu____3187 phi
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env ->
    fun d ->
      fun s ->
        let uu____3220 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")) in
        if uu____3220
        then
          let uu____3228 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d) in
          let uu____3231 = prob_to_string env d in
          let uu____3233 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>") in
          let uu____3240 = FStar_Thunk.force s in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3228 uu____3231 uu____3233 uu____3240
        else
          (let d1 = maybe_invert_p d in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ -> "equal to"
             | FStar_TypeChecker_Common.SUB -> "a subtype of"
             | uu____3252 -> failwith "impossible" in
           let uu____3255 =
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
           match uu____3255 with
           | (lhs, rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
let (commit : uvi Prims.list -> unit) =
  fun uvis ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3298 ->
            match uu___15_3298 with
            | UNIV (u, t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3312 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u, t) ->
                ((let uu____3316 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3316 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv ->
    fun s ->
      FStar_Util.find_map s
        (fun uu___16_3347 ->
           match uu___16_3347 with
           | UNIV uu____3350 -> FStar_Pervasives_Native.None
           | TERM (u, t) ->
               let uu____3357 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head in
               if uu____3357
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
        (fun uu___17_3385 ->
           match uu___17_3385 with
           | UNIV (u', t) ->
               let uu____3390 = FStar_Syntax_Unionfind.univ_equiv u u' in
               if uu____3390
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3397 -> FStar_Pervasives_Native.None)
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____3409 =
        let uu____3410 =
          let uu____3411 = FStar_Syntax_Util.unmeta t in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3411 in
        FStar_Syntax_Subst.compress uu____3410 in
      FStar_All.pipe_right uu____3409 FStar_Syntax_Util.unlazy_emb
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____3423 =
        let uu____3424 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t in
        FStar_Syntax_Subst.compress uu____3424 in
      FStar_All.pipe_right uu____3423 FStar_Syntax_Util.unlazy_emb
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____3436 =
        let uu____3440 =
          let uu____3442 = FStar_TypeChecker_Env.current_module env in
          FStar_Ident.string_of_lid uu____3442 in
        FStar_Pervasives_Native.Some uu____3440 in
      FStar_Profiling.profile (fun uu____3445 -> sn' env t) uu____3436
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
          let uu____3470 =
            let uu____3474 =
              let uu____3476 = FStar_TypeChecker_Env.current_module env in
              FStar_Ident.string_of_lid uu____3476 in
            FStar_Pervasives_Native.Some uu____3474 in
          FStar_Profiling.profile
            (fun uu____3479 ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3470
            profiling_tag
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____3487 = FStar_Syntax_Util.head_and_args t in
    match uu____3487 with
    | (h, uu____3506) ->
        let uu____3531 =
          let uu____3532 = FStar_Syntax_Subst.compress h in
          uu____3532.FStar_Syntax_Syntax.n in
        (match uu____3531 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> true
         | uu____3537 -> false)
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      let uu____3550 =
        let uu____3554 =
          let uu____3556 = FStar_TypeChecker_Env.current_module env in
          FStar_Ident.string_of_lid uu____3556 in
        FStar_Pervasives_Native.Some uu____3554 in
      FStar_Profiling.profile
        (fun uu____3561 ->
           let uu____3562 = should_strongly_reduce t in
           if uu____3562
           then
             let uu____3565 =
               let uu____3566 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t in
               FStar_Syntax_Subst.compress uu____3566 in
             FStar_All.pipe_right uu____3565 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3550 "FStar.TypeChecker.Rel.whnf"
let norm_arg :
  'uuuuuu3577 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu3577) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu3577)
  =
  fun env ->
    fun t ->
      let uu____3600 = sn env (FStar_Pervasives_Native.fst t) in
      (uu____3600, (FStar_Pervasives_Native.snd t))
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
           (fun uu____3652 ->
              match uu____3652 with
              | (x, imp) ->
                  let uu____3671 =
                    let uu___484_3672 = x in
                    let uu____3673 = sn env x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___484_3672.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___484_3672.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3673
                    } in
                  (uu____3671, imp)))
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl ->
    fun u ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1 in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3697 = aux u3 in FStar_Syntax_Syntax.U_succ uu____3697
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3701 = FStar_List.map aux us in
            FStar_Syntax_Syntax.U_max uu____3701
        | uu____3704 -> u2 in
      let uu____3705 = aux u in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3705
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps ->
    fun env ->
      fun t0 ->
        let uu____3722 =
          let uu____3726 =
            let uu____3728 = FStar_TypeChecker_Env.current_module env in
            FStar_Ident.string_of_lid uu____3728 in
          FStar_Pervasives_Native.Some uu____3726 in
        FStar_Profiling.profile
          (fun uu____3731 ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3722 "FStar.TypeChecker.Rel.normalize_refinement"
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
                (let uu____3853 = norm_refinement env t12 in
                 match uu____3853 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1, phi1);
                     FStar_Syntax_Syntax.pos = uu____3868;
                     FStar_Syntax_Syntax.vars = uu____3869;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3893 =
                       let uu____3895 = FStar_Syntax_Print.term_to_string tt in
                       let uu____3897 = FStar_Syntax_Print.tag_of_term tt in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3895 uu____3897 in
                     failwith uu____3893)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3913 = FStar_Syntax_Util.unfold_lazy i in
              aux norm uu____3913
          | FStar_Syntax_Syntax.Tm_uinst uu____3914 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____3951 =
                   let uu____3952 = FStar_Syntax_Subst.compress t1' in
                   uu____3952.FStar_Syntax_Syntax.n in
                 match uu____3951 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3967 -> aux true t1'
                 | uu____3975 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3990 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____4021 =
                   let uu____4022 = FStar_Syntax_Subst.compress t1' in
                   uu____4022.FStar_Syntax_Syntax.n in
                 match uu____4021 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4037 -> aux true t1'
                 | uu____4045 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4060 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12 in
                 let uu____4107 =
                   let uu____4108 = FStar_Syntax_Subst.compress t1' in
                   uu____4108.FStar_Syntax_Syntax.n in
                 match uu____4107 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4123 -> aux true t1'
                 | uu____4131 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____4146 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____4161 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____4176 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____4191 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____4206 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____4235 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____4268 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____4289 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____4316 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____4344 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____4381 ->
              let uu____4388 =
                let uu____4390 = FStar_Syntax_Print.term_to_string t12 in
                let uu____4392 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4390 uu____4392 in
              failwith uu____4388
          | FStar_Syntax_Syntax.Tm_ascribed uu____4407 ->
              let uu____4434 =
                let uu____4436 = FStar_Syntax_Print.term_to_string t12 in
                let uu____4438 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4436 uu____4438 in
              failwith uu____4434
          | FStar_Syntax_Syntax.Tm_delayed uu____4453 ->
              let uu____4468 =
                let uu____4470 = FStar_Syntax_Print.term_to_string t12 in
                let uu____4472 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4470 uu____4472 in
              failwith uu____4468
          | FStar_Syntax_Syntax.Tm_unknown ->
              let uu____4487 =
                let uu____4489 = FStar_Syntax_Print.term_to_string t12 in
                let uu____4491 = FStar_Syntax_Print.tag_of_term t12 in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4489 uu____4491 in
              failwith uu____4487 in
        let uu____4506 = whnf env t1 in aux false uu____4506
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
      let uu____4551 = base_and_refinement env t in
      FStar_All.pipe_right uu____4551 FStar_Pervasives_Native.fst
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t ->
    let uu____4592 = FStar_Syntax_Syntax.null_bv t in
    (uu____4592, FStar_Syntax_Util.t_true)
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta ->
    fun env ->
      fun t ->
        let uu____4619 = base_and_refinement_maybe_delta delta env t in
        match uu____4619 with
        | (t_base, refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x, phi) -> (x, phi))
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4679 ->
    match uu____4679 with
    | (t_base, refopt) ->
        let uu____4710 =
          match refopt with
          | FStar_Pervasives_Native.Some (y, phi) -> (y, phi)
          | FStar_Pervasives_Native.None -> trivial_refinement t_base in
        (match uu____4710 with
         | (y, phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               t_base.FStar_Syntax_Syntax.pos)
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl -> fun prob -> prob_to_string wl.tcenv prob
let (wl_to_string : worklist -> Prims.string) =
  fun wl ->
    let uu____4752 =
      let uu____4756 =
        let uu____4759 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4784 ->
                  match uu____4784 with | (uu____4792, uu____4793, x) -> x)) in
        FStar_List.append wl.attempting uu____4759 in
      FStar_List.map (wl_prob_to_string wl) uu____4756 in
    FStar_All.pipe_right uu____4752 (FStar_String.concat "\n\t")
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
  fun uu____4853 ->
    match uu____4853 with
    | Flex (uu____4855, u, uu____4857) ->
        u.FStar_Syntax_Syntax.ctx_uvar_reason
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4864 ->
    match uu____4864 with
    | Flex (uu____4866, c, args) ->
        let uu____4869 = print_ctx_uvar c in
        let uu____4871 = FStar_Syntax_Print.args_to_string args in
        FStar_Util.format2 "%s [%s]" uu____4869 uu____4871
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____4881 = FStar_Syntax_Util.head_and_args t in
    match uu____4881 with
    | (head, _args) ->
        let uu____4925 =
          let uu____4926 = FStar_Syntax_Subst.compress head in
          uu____4926.FStar_Syntax_Syntax.n in
        (match uu____4925 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4930 -> true
         | uu____4944 -> false)
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t ->
    let uu____4952 = FStar_Syntax_Util.head_and_args t in
    match uu____4952 with
    | (head, _args) ->
        let uu____4995 =
          let uu____4996 = FStar_Syntax_Subst.compress head in
          uu____4996.FStar_Syntax_Syntax.n in
        (match uu____4995 with
         | FStar_Syntax_Syntax.Tm_uvar (u, uu____5000) -> u
         | uu____5017 -> failwith "Not a flex-uvar")
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0 ->
    fun wl ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x in
        let t_x' = FStar_Syntax_Subst.subst' s t_x in
        let uu____5053 =
          let uu____5054 = FStar_Syntax_Subst.compress t_x' in
          uu____5054.FStar_Syntax_Syntax.n in
        match uu____5053 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____5059 -> false in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____5075 -> true in
      let uu____5077 = FStar_Syntax_Util.head_and_args t0 in
      match uu____5077 with
      | (head, args) ->
          let uu____5124 =
            let uu____5125 = FStar_Syntax_Subst.compress head in
            uu____5125.FStar_Syntax_Syntax.n in
          (match uu____5124 with
           | FStar_Syntax_Syntax.Tm_uvar (uv, ([], uu____5133)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv, uu____5149) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv, s) ->
               let uu____5190 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma in
               (match uu____5190 with
                | (gamma_aff, new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____5217 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff in
                         let uu____5221 =
                           let uu____5228 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma in
                           let uu____5237 =
                             let uu____5240 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ in
                             FStar_Syntax_Util.arrow dom_binders uu____5240 in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____5228
                             uu____5237
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta in
                         (match uu____5221 with
                          | (v, t_v, wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____5276 ->
                                     match uu____5276 with
                                     | (x, i) ->
                                         let uu____5295 =
                                           FStar_Syntax_Syntax.bv_to_name x in
                                         (uu____5295, i)) dom_binders in
                              let sol =
                                FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                  t0.FStar_Syntax_Syntax.pos in
                              (FStar_Syntax_Util.set_uvar
                                 uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                               (let args_sol_s =
                                  FStar_List.map
                                    (fun uu____5325 ->
                                       match uu____5325 with
                                       | (a, i) ->
                                           let uu____5344 =
                                             FStar_Syntax_Subst.subst' s a in
                                           (uu____5344, i)) args_sol in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    t0.FStar_Syntax_Syntax.pos in
                                (t, wl1))))))
           | uu____5354 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t ->
    let uu____5366 = FStar_Syntax_Util.head_and_args t in
    match uu____5366 with
    | (head, args) ->
        let uu____5409 =
          let uu____5410 = FStar_Syntax_Subst.compress head in
          uu____5410.FStar_Syntax_Syntax.n in
        (match uu____5409 with
         | FStar_Syntax_Syntax.Tm_uvar (uv, s) -> Flex (t, uv, args)
         | uu____5431 -> failwith "Not a flex-uvar")
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t ->
    fun wl ->
      let uu____5452 = ensure_no_uvar_subst t wl in
      match uu____5452 with
      | (t1, wl1) ->
          let uu____5463 = destruct_flex_t' t1 in (uu____5463, wl1)
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k ->
    fun ys ->
      fun t ->
        let uu____5480 =
          let uu____5503 =
            let uu____5504 = FStar_Syntax_Subst.compress k in
            uu____5504.FStar_Syntax_Syntax.n in
          match uu____5503 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5586 = FStar_Syntax_Subst.open_comp bs c in
                ((ys, t), uu____5586)
              else
                (let uu____5621 = FStar_Syntax_Util.abs_formals t in
                 match uu____5621 with
                 | (ys', t1, uu____5654) ->
                     let uu____5659 = FStar_Syntax_Util.arrow_formals_comp k in
                     (((FStar_List.append ys ys'), t1), uu____5659))
          | uu____5698 ->
              let uu____5699 =
                let uu____5704 = FStar_Syntax_Syntax.mk_Total k in
                ([], uu____5704) in
              ((ys, t), uu____5699) in
        match uu____5480 with
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
                 let uu____5799 = FStar_Syntax_Util.rename_binders xs ys1 in
                 FStar_Syntax_Subst.subst_comp uu____5799 c in
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
               (let uu____5877 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel") in
                if uu____5877
                then
                  let uu____5882 = FStar_Util.string_of_int (p_pid prob) in
                  let uu____5884 = print_ctx_uvar uv in
                  let uu____5886 = FStar_Syntax_Print.term_to_string phi1 in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5882 uu____5884 uu____5886
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0)) in
                (let uu____5895 =
                   let uu____5897 = FStar_Util.string_of_int (p_pid prob) in
                   Prims.op_Hat "solve_prob'.sol." uu____5897 in
                 let uu____5900 =
                   let uu____5903 = p_scope prob in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5903 in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5895 uu____5900 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2) in
             let uv = p_guard_uvar prob in
             let fail uu____5936 =
               let uu____5937 =
                 let uu____5939 = FStar_Syntax_Print.ctx_uvar_to_string uv in
                 let uu____5941 =
                   FStar_Syntax_Print.term_to_string (p_guard prob) in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5939 uu____5941 in
               failwith uu____5937 in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____6007 ->
                       match uu____6007 with
                       | (a, i) ->
                           let uu____6028 =
                             let uu____6029 = FStar_Syntax_Subst.compress a in
                             uu____6029.FStar_Syntax_Syntax.n in
                           (match uu____6028 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____6055 -> (fail (); [])))) in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob) in
               let uu____6065 =
                 let uu____6067 = is_flex g in Prims.op_Negation uu____6067 in
               if uu____6065
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____6076 = destruct_flex_t g wl in
                  match uu____6076 with
                  | (Flex (uu____6081, uv1, args), wl1) ->
                      ((let uu____6086 = args_as_binders args in
                        assign_solution uu____6086 uv1 phi);
                       wl1)) in
             commit uvis;
             (let uu___762_6088 = wl1 in
              {
                attempting = (uu___762_6088.attempting);
                wl_deferred = (uu___762_6088.wl_deferred);
                wl_deferred_to_tac = (uu___762_6088.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___762_6088.defer_ok);
                smt_ok = (uu___762_6088.smt_ok);
                umax_heuristic_ok = (uu___762_6088.umax_heuristic_ok);
                tcenv = (uu___762_6088.tcenv);
                wl_implicits = (uu___762_6088.wl_implicits);
                repr_subcomp_allowed = (uu___762_6088.repr_subcomp_allowed)
              }))
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid ->
    fun sol ->
      fun wl ->
        (let uu____6113 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel") in
         if uu____6113
         then
           let uu____6118 = FStar_Util.string_of_int pid in
           let uu____6120 = uvis_to_string wl.tcenv sol in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6118 uu____6120
         else ());
        commit sol;
        (let uu___770_6126 = wl in
         {
           attempting = (uu___770_6126.attempting);
           wl_deferred = (uu___770_6126.wl_deferred);
           wl_deferred_to_tac = (uu___770_6126.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___770_6126.defer_ok);
           smt_ok = (uu___770_6126.smt_ok);
           umax_heuristic_ok = (uu___770_6126.umax_heuristic_ok);
           tcenv = (uu___770_6126.tcenv);
           wl_implicits = (uu___770_6126.wl_implicits);
           repr_subcomp_allowed = (uu___770_6126.repr_subcomp_allowed)
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
          (let uu____6162 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel") in
           if uu____6162
           then
             let uu____6167 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob) in
             let uu____6171 = uvis_to_string wl.tcenv uvis in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6167 uu____6171
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
        let uu____6198 = FStar_Syntax_Free.uvars t in
        FStar_All.pipe_right uu____6198 FStar_Util.set_elements in
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
      let uu____6238 = occurs uk t in
      match uu____6238 with
      | (uvars, occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6277 =
                 let uu____6279 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head in
                 let uu____6281 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6279 uu____6281 in
               FStar_Pervasives_Native.Some uu____6277) in
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
          let uu____6392 = FStar_Syntax_Syntax.bv_eq b b' in
          if uu____6392
          then
            let uu____6403 = maximal_prefix bs_tail bs'_tail in
            (match uu____6403 with | (pfx, rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6454 -> ([], (bs, bs'))
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      FStar_List.fold_left
        (fun g1 ->
           fun uu____6511 ->
             match uu____6511 with
             | (x, uu____6523) -> (FStar_Syntax_Syntax.Binding_var x) :: g1)
        g bs
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g ->
    fun bs ->
      let uu____6541 = FStar_List.last bs in
      match uu____6541 with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some (x, uu____6565) ->
          let uu____6576 =
            FStar_Util.prefix_until
              (fun uu___18_6591 ->
                 match uu___18_6591 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6594 -> false) g in
          (match uu____6576 with
           | FStar_Pervasives_Native.None -> []
           | FStar_Pervasives_Native.Some (uu____6608, bx, rest) -> bx ::
               rest)
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt ->
    fun src ->
      fun wl ->
        let uu____6645 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders in
        match uu____6645 with
        | (pfx, uu____6655) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx in
            let uu____6667 =
              let uu____6674 =
                let uu____6676 =
                  FStar_Syntax_Print.uvar_to_string
                    src.FStar_Syntax_Syntax.ctx_uvar_head in
                Prims.op_Hat "restricted " uu____6676 in
              new_uvar uu____6674 wl src.FStar_Syntax_Syntax.ctx_uvar_range g
                pfx src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta in
            (match uu____6667 with
             | (uu____6679, src', wl1) ->
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
                 | uu____6793 -> out) FStar_Syntax_Syntax.no_names g in
        let uu____6794 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6858 ->
                  fun uu____6859 ->
                    match (uu____6858, uu____6859) with
                    | ((isect, isect_set), (x, imp)) ->
                        let uu____6962 =
                          let uu____6964 = FStar_Util.set_mem x v1_set in
                          FStar_All.pipe_left Prims.op_Negation uu____6964 in
                        if uu____6962
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort in
                           let uu____6998 =
                             FStar_Util.set_is_subset_of fvs isect_set in
                           if uu____6998
                           then
                             let uu____7015 = FStar_Util.set_add x isect_set in
                             (((x, imp) :: isect), uu____7015)
                           else (isect, isect_set))) ([], ctx_binders)) in
        match uu____6794 with | (isect, uu____7065) -> FStar_List.rev isect
let binders_eq :
  'uuuuuu7101 'uuuuuu7102 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu7101) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7102) Prims.list -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7160 ->
              fun uu____7161 ->
                match (uu____7160, uu____7161) with
                | ((a, uu____7180), (b, uu____7182)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let name_exists_in_binders :
  'uuuuuu7198 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7198) Prims.list -> Prims.bool
  =
  fun x ->
    fun bs ->
      FStar_Util.for_some
        (fun uu____7229 ->
           match uu____7229 with
           | (y, uu____7236) -> FStar_Syntax_Syntax.bv_eq x y) bs
let pat_vars :
  'uuuuuu7246 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7246) Prims.list ->
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
                   let uu____7408 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx) in
                   if uu____7408
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7441 -> FStar_Pervasives_Native.None) in
        aux [] args
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu____7493 -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | HeadMatch _0 -> true | uu____7537 -> false
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee -> match projectee with | HeadMatch _0 -> _0
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | FullMatch -> true | uu____7558 -> false
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7566 ->
    match uu___19_7566 with
    | MisMatch (d1, d2) ->
        let uu____7578 =
          let uu____7580 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1 in
          let uu____7582 =
            let uu____7584 =
              let uu____7586 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2 in
              Prims.op_Hat uu____7586 ")" in
            Prims.op_Hat ") (" uu____7584 in
          Prims.op_Hat uu____7580 uu____7582 in
        Prims.op_Hat "MisMatch (" uu____7578
    | HeadMatch u ->
        let uu____7593 = FStar_Util.string_of_bool u in
        Prims.op_Hat "HeadMatch " uu____7593
    | FullMatch -> "FullMatch"
let (head_match : match_result -> match_result) =
  fun uu___20_7602 ->
    match uu___20_7602 with
    | MisMatch (i, j) -> MisMatch (i, j)
    | HeadMatch (true) -> HeadMatch true
    | uu____7619 -> HeadMatch false
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env ->
    fun fv ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7634 =
            (let uu____7640 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule in
             let uu____7642 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             uu____7640 = uu____7642) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) in
          if uu____7634 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7651 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____7651 with
           | FStar_Pervasives_Native.None ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7662 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7686 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7696 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7715 = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env uu____7715
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7716 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7717 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7718 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7731 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7745 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____7769) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____7775, uu____7776) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2, uu____7818) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7843;
             FStar_Syntax_Syntax.index = uu____7844;
             FStar_Syntax_Syntax.sort = t2;_},
           uu____7846)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7854 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7855 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7856 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7871 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7878 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7898 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____7898
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
           { FStar_Syntax_Syntax.blob = uu____7917;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7918;
             FStar_Syntax_Syntax.ltyp = uu____7919;
             FStar_Syntax_Syntax.rng = uu____7920;_},
           uu____7921) ->
            let uu____7932 = FStar_Syntax_Util.unlazy t11 in
            head_matches env uu____7932 t21
        | (uu____7933, FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7934;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7935;
             FStar_Syntax_Syntax.ltyp = uu____7936;
             FStar_Syntax_Syntax.rng = uu____7937;_})
            ->
            let uu____7948 = FStar_Syntax_Util.unlazy t21 in
            head_matches env t11 uu____7948
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7951 = FStar_Syntax_Syntax.bv_eq x y in
            if uu____7951
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7962 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____7962
            then FullMatch
            else
              (let uu____7967 =
                 let uu____7976 =
                   let uu____7979 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____7979 in
                 let uu____7980 =
                   let uu____7983 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____7983 in
                 (uu____7976, uu____7980) in
               MisMatch uu____7967)
        | (FStar_Syntax_Syntax.Tm_uinst (f, uu____7989),
           FStar_Syntax_Syntax.Tm_uinst (g, uu____7991)) ->
            let uu____8000 = head_matches env f g in
            FStar_All.pipe_right uu____8000 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           uu____8001) -> HeadMatch true
        | (uu____8003, FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify)) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____8007 = FStar_Const.eq_const c d in
            if uu____8007
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar (uv, uu____8017),
           FStar_Syntax_Syntax.Tm_uvar (uv', uu____8019)) ->
            let uu____8052 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head in
            if uu____8052
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____8062),
           FStar_Syntax_Syntax.Tm_refine (y, uu____8064)) ->
            let uu____8073 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____8073 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____8075), uu____8076) ->
            let uu____8081 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____8081 head_match
        | (uu____8082, FStar_Syntax_Syntax.Tm_refine (x, uu____8084)) ->
            let uu____8089 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____8089 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8090,
           FStar_Syntax_Syntax.Tm_type uu____8091) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow uu____8093,
           FStar_Syntax_Syntax.Tm_arrow uu____8094) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app (head, uu____8125),
           FStar_Syntax_Syntax.Tm_app (head', uu____8127)) ->
            let uu____8176 = head_matches env head head' in
            FStar_All.pipe_right uu____8176 head_match
        | (FStar_Syntax_Syntax.Tm_app (head, uu____8178), uu____8179) ->
            let uu____8204 = head_matches env head t21 in
            FStar_All.pipe_right uu____8204 head_match
        | (uu____8205, FStar_Syntax_Syntax.Tm_app (head, uu____8207)) ->
            let uu____8232 = head_matches env t11 head in
            FStar_All.pipe_right uu____8232 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8233, FStar_Syntax_Syntax.Tm_let
           uu____8234) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match uu____8262,
           FStar_Syntax_Syntax.Tm_match uu____8263) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8309, FStar_Syntax_Syntax.Tm_abs
           uu____8310) -> HeadMatch true
        | uu____8348 ->
            let uu____8353 =
              let uu____8362 = delta_depth_of_term env t11 in
              let uu____8365 = delta_depth_of_term env t21 in
              (uu____8362, uu____8365) in
            MisMatch uu____8353
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
              let uu____8434 = unrefine env t in
              FStar_Syntax_Util.head_of uu____8434 in
            (let uu____8436 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____8436
             then
               let uu____8441 = FStar_Syntax_Print.term_to_string t in
               let uu____8443 = FStar_Syntax_Print.term_to_string head in
               FStar_Util.print2 "Head of %s is %s\n" uu____8441 uu____8443
             else ());
            (let uu____8448 =
               let uu____8449 = FStar_Syntax_Util.un_uinst head in
               uu____8449.FStar_Syntax_Syntax.n in
             match uu____8448 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8455 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 (match uu____8455 with
                  | FStar_Pervasives_Native.None ->
                      ((let uu____8469 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta") in
                        if uu____8469
                        then
                          let uu____8474 =
                            FStar_Syntax_Print.term_to_string head in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8474
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8479 ->
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
                      let uu____8497 =
                        let uu____8499 = FStar_Syntax_Util.eq_tm t t' in
                        uu____8499 = FStar_Syntax_Util.Equal in
                      if uu____8497
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8506 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta") in
                          if uu____8506
                          then
                            let uu____8511 =
                              FStar_Syntax_Print.term_to_string t in
                            let uu____8513 =
                              FStar_Syntax_Print.term_to_string t' in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8511
                              uu____8513
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8518 -> FStar_Pervasives_Native.None) in
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
            (let uu____8670 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____8670
             then
               let uu____8675 = FStar_Syntax_Print.term_to_string t11 in
               let uu____8677 = FStar_Syntax_Print.term_to_string t21 in
               let uu____8679 = string_of_match_result r in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8675
                 uu____8677 uu____8679
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
               let uu____8707 =
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
               match uu____8707 with
               | (t12, t22) -> aux retry (n_delta + Prims.int_one) t12 t22 in
             let reduce_both_and_try_again d r1 =
               let uu____8755 = FStar_TypeChecker_Common.decr_delta_depth d in
               match uu____8755 with
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
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8793),
                  uu____8794)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8815 =
                      let uu____8824 = maybe_inline t11 in
                      let uu____8827 = maybe_inline t21 in
                      (uu____8824, uu____8827) in
                    match uu____8815 with
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
                 (uu____8870, FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8871))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8892 =
                      let uu____8901 = maybe_inline t11 in
                      let uu____8904 = maybe_inline t21 in
                      (uu____8901, uu____8904) in
                    match uu____8892 with
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
             | MisMatch uu____8959 -> fail n_delta r t11 t21
             | uu____8968 -> success n_delta r t11 t21) in
          let r = aux true Prims.int_zero t1 t2 in
          (let uu____8983 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta") in
           if uu____8983
           then
             let uu____8988 = FStar_Syntax_Print.term_to_string t1 in
             let uu____8990 = FStar_Syntax_Print.term_to_string t2 in
             let uu____8992 =
               string_of_match_result (FStar_Pervasives_Native.fst r) in
             let uu____9000 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____9017 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must in
                  FStar_All.pipe_right uu____9017
                    (fun uu____9052 ->
                       match uu____9052 with
                       | (t11, t21) ->
                           let uu____9060 =
                             FStar_Syntax_Print.term_to_string t11 in
                           let uu____9062 =
                             let uu____9064 =
                               FStar_Syntax_Print.term_to_string t21 in
                             Prims.op_Hat "; " uu____9064 in
                           Prims.op_Hat uu____9060 uu____9062)) in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8988 uu____8990 uu____8992 uu____9000
           else ());
          r
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu____9081 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____9081 FStar_Pervasives_Native.fst
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_9096 ->
    match uu___21_9096 with
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
      let uu___1259_9145 = p in
      let uu____9148 = whnf tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____9149 = whnf tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1259_9145.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9148;
        FStar_TypeChecker_Common.relation =
          (uu___1259_9145.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9149;
        FStar_TypeChecker_Common.element =
          (uu___1259_9145.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1259_9145.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1259_9145.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1259_9145.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1259_9145.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1259_9145.FStar_TypeChecker_Common.rank)
      }
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv ->
    fun p ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9164 = compress_tprob tcenv p1 in
          FStar_All.pipe_right uu____9164
            (fun uu____9169 -> FStar_TypeChecker_Common.TProb uu____9169)
      | FStar_TypeChecker_Common.CProb uu____9170 -> p
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv ->
    fun pr ->
      let prob =
        let uu____9193 = compress_prob tcenv pr in
        FStar_All.pipe_right uu____9193 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9201 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____9201 with
           | (lh, lhs_args) ->
               let uu____9248 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____9248 with
                | (rh, rhs_args) ->
                    let uu____9295 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9308,
                         FStar_Syntax_Syntax.Tm_uvar uu____9309) ->
                          (match (lhs_args, rhs_args) with
                           | ([], []) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9398 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9425, uu____9426)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9441, FStar_Syntax_Syntax.Tm_uvar uu____9442)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9457,
                         FStar_Syntax_Syntax.Tm_arrow uu____9458) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9488 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_9488.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_9488.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_9488.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_9488.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_9488.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_9488.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_9488.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_9488.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_9488.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9491,
                         FStar_Syntax_Syntax.Tm_type uu____9492) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9508 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_9508.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_9508.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_9508.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_9508.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_9508.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_9508.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_9508.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_9508.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_9508.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type uu____9511,
                         FStar_Syntax_Syntax.Tm_uvar uu____9512) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9528 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_9528.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_9528.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_9528.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_9528.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_9528.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_9528.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_9528.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_9528.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_9528.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9531, FStar_Syntax_Syntax.Tm_uvar uu____9532)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9547, uu____9548)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9563, FStar_Syntax_Syntax.Tm_uvar uu____9564)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9579, uu____9580) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp) in
                    (match uu____9295 with
                     | (rank, tp1) ->
                         let uu____9593 =
                           FStar_All.pipe_right
                             (let uu___1330_9597 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1330_9597.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1330_9597.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1330_9597.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1330_9597.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1330_9597.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1330_9597.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1330_9597.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1330_9597.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1330_9597.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9600 ->
                                FStar_TypeChecker_Common.TProb uu____9600) in
                         (rank, uu____9593))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9604 =
            FStar_All.pipe_right
              (let uu___1334_9608 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1334_9608.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1334_9608.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1334_9608.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1334_9608.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1334_9608.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1334_9608.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1334_9608.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1334_9608.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1334_9608.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9611 -> FStar_TypeChecker_Common.CProb uu____9611) in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9604)
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl ->
    let rec aux uu____9671 probs =
      match uu____9671 with
      | (min_rank, min, out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some p,
                   FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9752 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9773 = rank wl.tcenv hd in
               (match uu____9773 with
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
                      (let uu____9834 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9839 = FStar_Option.get min_rank in
                            rank_less_than rank1 uu____9839) in
                       if uu____9834
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
          let uu____9912 = FStar_Syntax_Util.head_and_args t in
          match uu____9912 with
          | (hd, uu____9931) ->
              let uu____9956 =
                let uu____9957 = FStar_Syntax_Subst.compress hd in
                uu____9957.FStar_Syntax_Syntax.n in
              (match uu____9956 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu____9962) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9997 ->
                           match uu____9997 with
                           | (y, uu____10006) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____10029 ->
                                       match uu____10029 with
                                       | (x, uu____10038) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____10043 -> false) in
        let uu____10045 = rank tcenv p in
        match uu____10045 with
        | (r, p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____10054 -> true
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
    match projectee with | UDeferred _0 -> true | uu____10135 -> false
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | USolved _0 -> true | uu____10154 -> false
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UFailed _0 -> true | uu____10173 -> false
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee -> match projectee with | UFailed _0 -> _0
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s -> let uu____10190 = FStar_Thunk.mkv s in UFailed uu____10190
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s -> let uu____10205 = mklstr s in UFailed uu____10205
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
                        let uu____10256 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____10256 with
                        | (k, uu____10264) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10279 -> false)))
            | uu____10281 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs ->
                      fun uv1 ->
                        let uu____10333 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2 -> FStar_Syntax_Util.eq_univs uv1 uv2)) in
                        if uu____10333 then uv1 :: uvs else uvs) []) in
            let filter =
              FStar_List.filter
                (fun u ->
                   let uu____10357 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u' -> FStar_Syntax_Util.eq_univs u u')) in
                   Prims.op_Negation uu____10357) in
            let uu____10364 = filter u12 in
            let uu____10367 = filter u22 in (uu____10364, uu____10367) in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10402 = filter_out_common_univs us1 us2 in
                   (match uu____10402 with
                    | (us11, us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13, u23::us23) ->
                                let uu____10462 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23 in
                                (match uu____10462 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10465 -> USolved wl1 in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10482 ->
                               let uu____10483 =
                                 FStar_Syntax_Print.univ_to_string u12 in
                               let uu____10485 =
                                 FStar_Syntax_Print.univ_to_string u22 in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10483 uu____10485))
               | (FStar_Syntax_Syntax.U_max us, u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10511 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____10511 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | (u', FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10537 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____10537 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | uu____10540 ->
                   ufailed_thunk
                     (fun uu____10551 ->
                        let uu____10552 =
                          FStar_Syntax_Print.univ_to_string u12 in
                        let uu____10554 =
                          FStar_Syntax_Print.univ_to_string u22 in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10552 uu____10554 msg)) in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10557, uu____10558) ->
              let uu____10560 =
                let uu____10562 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10564 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10562 uu____10564 in
              failwith uu____10560
          | (FStar_Syntax_Syntax.U_unknown, uu____10567) ->
              let uu____10568 =
                let uu____10570 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10572 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10570 uu____10572 in
              failwith uu____10568
          | (uu____10575, FStar_Syntax_Syntax.U_bvar uu____10576) ->
              let uu____10578 =
                let uu____10580 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10582 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10580 uu____10582 in
              failwith uu____10578
          | (uu____10585, FStar_Syntax_Syntax.U_unknown) ->
              let uu____10586 =
                let uu____10588 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10590 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10588 uu____10590 in
              failwith uu____10586
          | (FStar_Syntax_Syntax.U_name x, FStar_Syntax_Syntax.U_name y) ->
              let uu____10595 =
                let uu____10597 = FStar_Ident.string_of_id x in
                let uu____10599 = FStar_Ident.string_of_id y in
                uu____10597 = uu____10599 in
              if uu____10595
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12, FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1, FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10630 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____10630
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu____10649 = occurs_univ v1 u3 in
              if uu____10649
              then
                let uu____10652 =
                  let uu____10654 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____10656 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10654 uu____10656 in
                try_umax_components u11 u21 uu____10652
              else
                (let uu____10661 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____10661)
          | (u, FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____10675 = occurs_univ v1 u3 in
              if uu____10675
              then
                let uu____10678 =
                  let uu____10680 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____10682 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10680 uu____10682 in
                try_umax_components u11 u21 uu____10678
              else
                (let uu____10687 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____10687)
          | (FStar_Syntax_Syntax.U_max uu____10688, uu____10689) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____10697 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____10697
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10703, FStar_Syntax_Syntax.U_max uu____10704) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____10712 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____10712
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____10718,
             FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____10720,
             FStar_Syntax_Syntax.U_name uu____10721) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ
             uu____10723) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name
             uu____10725) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____10727,
             FStar_Syntax_Syntax.U_succ uu____10728) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____10730,
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
      let uu____10837 = bc1 in
      match uu____10837 with
      | (bs1, mk_cod1) ->
          let uu____10881 = bc2 in
          (match uu____10881 with
           | (bs2, mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs, y::ys) ->
                     let uu____10992 = aux xs ys in
                     (match uu____10992 with
                      | ((xs1, xr), (ys1, yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs, ys) ->
                     let uu____11075 =
                       let uu____11082 = mk_cod1 xs in ([], uu____11082) in
                     let uu____11085 =
                       let uu____11092 = mk_cod2 ys in ([], uu____11092) in
                     (uu____11075, uu____11085) in
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
                  let uu____11161 = FStar_Syntax_Syntax.bv_to_name t in
                  FStar_Syntax_Util.mk_has_type t11 uu____11161 t21
              | FStar_Pervasives_Native.None ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11 in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11 in
                  let uu____11164 =
                    let uu____11165 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Util.mk_has_type t11 uu____11165 t21 in
                  FStar_Syntax_Util.mk_forall u_x x uu____11164 in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB ->
                let uu____11170 = has_type_guard t1 t2 in (uu____11170, wl)
            | FStar_TypeChecker_Common.SUBINV ->
                let uu____11171 = has_type_guard t2 t1 in (uu____11171, wl)
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_11178 ->
    match uu___22_11178 with
    | Flex (uu____11180, uu____11181, []) -> true
    | uu____11191 -> false
let (should_defer_flex_to_user_tac :
  FStar_TypeChecker_Env.env -> worklist -> flex_t -> Prims.bool) =
  fun env ->
    fun wl ->
      fun f ->
        let uu____11210 = f in
        match uu____11210 with
        | Flex (uu____11212, u, uu____11214) ->
            let b =
              FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                wl.tcenv u in
            ((let uu____11218 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ResolveImplicitsHook") in
              if uu____11218
              then
                let uu____11223 =
                  FStar_Syntax_Print.ctx_uvar_to_string_no_reason u in
                let uu____11225 = FStar_Util.string_of_bool b in
                FStar_Util.print2
                  "Rel.should_defer_flex_to_user_tac for %s returning %s\n"
                  uu____11223 uu____11225
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
      let uu____11253 = f in
      match uu____11253 with
      | Flex
          (uu____11260,
           { FStar_Syntax_Syntax.ctx_uvar_head = uu____11261;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11262;
             FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
             FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____11265;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____11266;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____11267;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____11268;_},
           args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11334 ->
                 match uu____11334 with
                 | (y, uu____11343) -> FStar_Syntax_Syntax.bv_eq x y) bs in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([], []) ->
                let uu____11497 =
                  let uu____11512 =
                    let uu____11515 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____11515 in
                  ((FStar_List.rev pat_binders), uu____11512) in
                FStar_Pervasives_Native.Some uu____11497
            | (uu____11548, []) ->
                let uu____11579 =
                  let uu____11594 =
                    let uu____11597 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____11597 in
                  ((FStar_List.rev pat_binders), uu____11594) in
                FStar_Pervasives_Native.Some uu____11579
            | ((formal, formal_imp)::formals1, (a, a_imp)::args2) ->
                let uu____11688 =
                  let uu____11689 = FStar_Syntax_Subst.compress a in
                  uu____11689.FStar_Syntax_Syntax.n in
                (match uu____11688 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11709 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders) in
                     if uu____11709
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1675_11739 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1675_11739.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1675_11739.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          } in
                        let subst =
                          let uu____11743 =
                            let uu____11744 =
                              let uu____11751 =
                                FStar_Syntax_Syntax.bv_to_name x1 in
                              (formal, uu____11751) in
                            FStar_Syntax_Syntax.NT uu____11744 in
                          [uu____11743] in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1 in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res in
                        aux
                          (((let uu___1681_11767 = x1 in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1681_11767.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1681_11767.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11768 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([], args2) ->
                let uu____11808 =
                  let uu____11815 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res in
                  FStar_Syntax_Util.arrow_formals uu____11815 in
                (match uu____11808 with
                 | (more_formals, t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11874 ->
                          aux pat_binders more_formals t_res1 args2)) in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11899 ->
               let uu____11900 = FStar_Syntax_Util.arrow_formals t_hd in
               (match uu____11900 with
                | (formals, t_res) -> aux [] formals t_res args))
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env ->
    fun probs ->
      (let uu____12232 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel") in
       if uu____12232
       then
         let uu____12237 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12237
       else ());
      (let uu____12243 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace") in
       if uu____12243
       then
         let uu____12248 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12248
       else ());
      (let uu____12253 = next_prob probs in
       match uu____12253 with
       | FStar_Pervasives_Native.Some (hd, tl, rank1) ->
           let probs1 =
             let uu___1708_12280 = probs in
             {
               attempting = tl;
               wl_deferred = (uu___1708_12280.wl_deferred);
               wl_deferred_to_tac = (uu___1708_12280.wl_deferred_to_tac);
               ctr = (uu___1708_12280.ctr);
               defer_ok = (uu___1708_12280.defer_ok);
               smt_ok = (uu___1708_12280.smt_ok);
               umax_heuristic_ok = (uu___1708_12280.umax_heuristic_ok);
               tcenv = (uu___1708_12280.tcenv);
               wl_implicits = (uu___1708_12280.wl_implicits);
               repr_subcomp_allowed = (uu___1708_12280.repr_subcomp_allowed)
             } in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12289 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs in
                 if uu____12289
                 then
                   let uu____12292 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1 in
                   solve env uu____12292
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
                           (let uu___1720_12304 = tp in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1720_12304.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1720_12304.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1720_12304.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1720_12304.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1720_12304.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1720_12304.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1720_12304.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1720_12304.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1720_12304.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12324 =
                  let uu____12331 = as_deferred probs.wl_deferred_to_tac in
                  ([], uu____12331, (probs.wl_implicits)) in
                Success uu____12324
            | uu____12337 ->
                let uu____12347 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12412 ->
                          match uu____12412 with
                          | (c, uu____12422, uu____12423) -> c < probs.ctr)) in
                (match uu____12347 with
                 | (attempt1, rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12471 =
                            let uu____12478 = as_deferred probs.wl_deferred in
                            let uu____12479 =
                              as_deferred probs.wl_deferred_to_tac in
                            (uu____12478, uu____12479, (probs.wl_implicits)) in
                          Success uu____12471
                      | uu____12480 ->
                          let uu____12490 =
                            let uu___1734_12491 = probs in
                            let uu____12492 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12513 ->
                                      match uu____12513 with
                                      | (uu____12521, uu____12522, y) -> y)) in
                            {
                              attempting = uu____12492;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1734_12491.wl_deferred_to_tac);
                              ctr = (uu___1734_12491.ctr);
                              defer_ok = (uu___1734_12491.defer_ok);
                              smt_ok = (uu___1734_12491.smt_ok);
                              umax_heuristic_ok =
                                (uu___1734_12491.umax_heuristic_ok);
                              tcenv = (uu___1734_12491.tcenv);
                              wl_implicits = (uu___1734_12491.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1734_12491.repr_subcomp_allowed)
                            } in
                          solve env uu____12490))))
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
            let uu____12531 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____12531 with
            | USolved wl1 ->
                let uu____12533 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____12533
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12536 = defer_lit "" orig wl1 in
                solve env uu____12536
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
                  let uu____12587 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____12587 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12590 -> ufailed_simple "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12603;
                  FStar_Syntax_Syntax.vars = uu____12604;_},
                us1),
               FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12607;
                  FStar_Syntax_Syntax.vars = uu____12608;_},
                us2)) ->
                let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12621, uu____12622) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12630, FStar_Syntax_Syntax.Tm_uinst uu____12631) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12639 -> USolved wl
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
            ((let uu____12650 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____12650
              then
                let uu____12655 = prob_to_string env orig in
                let uu____12657 = FStar_Thunk.force msg in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12655 uu____12657
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
            let uu___1816_12672 = wl1 in
            let uu____12673 =
              let uu____12683 =
                let uu____12691 = FStar_Thunk.mkv reason in
                ((wl1.ctr), uu____12691, orig) in
              uu____12683 :: (wl1.wl_deferred_to_tac) in
            {
              attempting = (uu___1816_12672.attempting);
              wl_deferred = (uu___1816_12672.wl_deferred);
              wl_deferred_to_tac = uu____12673;
              ctr = (uu___1816_12672.ctr);
              defer_ok = (uu___1816_12672.defer_ok);
              smt_ok = (uu___1816_12672.smt_ok);
              umax_heuristic_ok = (uu___1816_12672.umax_heuristic_ok);
              tcenv = (uu___1816_12672.tcenv);
              wl_implicits = (uu___1816_12672.wl_implicits);
              repr_subcomp_allowed = (uu___1816_12672.repr_subcomp_allowed)
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
                let uu____12720 = FStar_Syntax_Util.head_and_args t in
                match uu____12720 with
                | (head, uu____12744) ->
                    let uu____12769 =
                      let uu____12770 = FStar_Syntax_Subst.compress head in
                      uu____12770.FStar_Syntax_Syntax.n in
                    (match uu____12769 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv, uu____12780) ->
                         let uu____12797 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv in
                         (uu____12797,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12801 -> (false, "")) in
              let uu____12806 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs in
              (match uu____12806 with
               | (l1, r1) ->
                   let uu____12819 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs in
                   (match uu____12819 with
                    | (l2, r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12836 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl in
                           solve env uu____12836)))
          | uu____12837 ->
              let uu____12838 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl in
              solve env uu____12838
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
               let uu____12924 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements" in
               match uu____12924 with
               | (p, wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3)) in
             let pairwise t1 t2 wl2 =
               (let uu____12979 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu____12979
                then
                  let uu____12984 = FStar_Syntax_Print.term_to_string t1 in
                  let uu____12986 = FStar_Syntax_Print.term_to_string t2 in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12984 uu____12986
                else ());
               (let uu____12991 = head_matches_delta env1 wl2 t1 t2 in
                match uu____12991 with
                | (mr, ts1) ->
                    (match mr with
                     | HeadMatch (true) ->
                         let uu____13037 = eq_prob t1 t2 wl2 in
                         (match uu____13037 with | (p, wl3) -> (t1, [p], wl3))
                     | MisMatch uu____13058 ->
                         let uu____13067 = eq_prob t1 t2 wl2 in
                         (match uu____13067 with | (p, wl3) -> (t1, [p], wl3))
                     | FullMatch ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false) ->
                         let uu____13117 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11, t21) ->
                               let uu____13132 =
                                 FStar_Syntax_Subst.compress t11 in
                               let uu____13133 =
                                 FStar_Syntax_Subst.compress t21 in
                               (uu____13132, uu____13133)
                           | FStar_Pervasives_Native.None ->
                               let uu____13138 =
                                 FStar_Syntax_Subst.compress t1 in
                               let uu____13139 =
                                 FStar_Syntax_Subst.compress t2 in
                               (uu____13138, uu____13139) in
                         (match uu____13117 with
                          | (t11, t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13170 =
                                  FStar_Syntax_Util.head_and_args t12 in
                                match uu____13170 with
                                | (t1_hd, t1_args) ->
                                    let uu____13215 =
                                      FStar_Syntax_Util.head_and_args t22 in
                                    (match uu____13215 with
                                     | (t2_hd, t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13281 =
                                              let uu____13288 =
                                                let uu____13299 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd in
                                                uu____13299 :: t1_args in
                                              let uu____13316 =
                                                let uu____13325 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd in
                                                uu____13325 :: t2_args in
                                              FStar_List.fold_left2
                                                (fun uu____13374 ->
                                                   fun uu____13375 ->
                                                     fun uu____13376 ->
                                                       match (uu____13374,
                                                               uu____13375,
                                                               uu____13376)
                                                       with
                                                       | ((probs, wl4),
                                                          (a1, uu____13426),
                                                          (a2, uu____13428))
                                                           ->
                                                           let uu____13465 =
                                                             eq_prob a1 a2
                                                               wl4 in
                                                           (match uu____13465
                                                            with
                                                            | (p, wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13288
                                                uu____13316 in
                                            match uu____13281 with
                                            | (probs, wl4) ->
                                                let wl' =
                                                  let uu___1919_13491 = wl4 in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1919_13491.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1919_13491.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1919_13491.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1919_13491.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1919_13491.repr_subcomp_allowed)
                                                  } in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____13502 =
                                                  solve env1 wl' in
                                                (match uu____13502 with
                                                 | Success
                                                     (uu____13505,
                                                      defer_to_tac, imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13509 =
                                                         extend_wl wl4
                                                           defer_to_tac imps in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13509))
                                                 | Failed uu____13510 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None)))) in
                              let combine t12 t22 wl3 =
                                let uu____13542 =
                                  base_and_refinement_maybe_delta false env1
                                    t12 in
                                match uu____13542 with
                                | (t1_base, p1_opt) ->
                                    let uu____13578 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22 in
                                    (match uu____13578 with
                                     | (t2_base, p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13677 =
                                               FStar_Syntax_Util.is_t_true t in
                                             if uu____13677
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
                                               let uu____13730 =
                                                 op phi11 phi21 in
                                               refine x1 uu____13730
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
                                               let uu____13762 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____13762
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
                                               let uu____13794 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____13794
                                           | uu____13797 -> t_base in
                                         let uu____13814 =
                                           try_eq t1_base t2_base wl3 in
                                         (match uu____13814 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13828 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt in
                                              (uu____13828, [], wl4)
                                          | FStar_Pervasives_Native.None ->
                                              let uu____13835 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12 in
                                              (match uu____13835 with
                                               | (t1_base1, p1_opt1) ->
                                                   let uu____13871 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22 in
                                                   (match uu____13871 with
                                                    | (t2_base1, p2_opt1) ->
                                                        let uu____13907 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3 in
                                                        (match uu____13907
                                                         with
                                                         | (p, wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1 in
                                                             (t, [p], wl4)))))) in
                              let uu____13931 = combine t11 t21 wl2 in
                              (match uu____13931 with
                               | (t12, ps, wl3) ->
                                   ((let uu____13964 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel") in
                                     if uu____13964
                                     then
                                       let uu____13969 =
                                         FStar_Syntax_Print.term_to_string
                                           t12 in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13969
                                     else ());
                                    (t12, ps, wl3)))))) in
             let rec aux uu____14011 ts1 =
               match uu____14011 with
               | (out, probs, wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____14074 = pairwise out t wl2 in
                        (match uu____14074 with
                         | (out1, probs', wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2)) in
             let uu____14110 =
               let uu____14121 = FStar_List.hd ts in (uu____14121, [], wl1) in
             let uu____14130 = FStar_List.tl ts in
             aux uu____14110 uu____14130 in
           let uu____14137 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs)) in
           match uu____14137 with
           | (this_flex, this_rigid) ->
               let uu____14163 =
                 let uu____14164 = FStar_Syntax_Subst.compress this_rigid in
                 uu____14164.FStar_Syntax_Syntax.n in
               (match uu____14163 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs, comp) ->
                    let uu____14189 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp in
                    if uu____14189
                    then
                      let uu____14192 = destruct_flex_t this_flex wl in
                      (match uu____14192 with
                       | (flex, wl1) ->
                           let uu____14199 = quasi_pattern env flex in
                           (match uu____14199 with
                            | FStar_Pervasives_Native.None ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                                ->
                                ((let uu____14218 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____14218
                                  then
                                    let uu____14223 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14223
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14230 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2029_14233 = tp in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2029_14233.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2029_14233.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2029_14233.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2029_14233.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2029_14233.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2029_14233.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2029_14233.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2029_14233.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2029_14233.FStar_TypeChecker_Common.rank)
                                }))] wl in
                       solve env uu____14230)
                | uu____14234 ->
                    ((let uu____14236 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____14236
                      then
                        let uu____14241 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14241
                      else ());
                     (let uu____14246 =
                        FStar_Syntax_Util.head_and_args this_flex in
                      match uu____14246 with
                      | (u, _args) ->
                          let uu____14289 =
                            let uu____14290 = FStar_Syntax_Subst.compress u in
                            uu____14290.FStar_Syntax_Syntax.n in
                          (match uu____14289 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst)
                               ->
                               let equiv t =
                                 let uu____14318 =
                                   FStar_Syntax_Util.head_and_args t in
                                 match uu____14318 with
                                 | (u', uu____14337) ->
                                     let uu____14362 =
                                       let uu____14363 = whnf env u' in
                                       uu____14363.FStar_Syntax_Syntax.n in
                                     (match uu____14362 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar', _subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14385 -> false) in
                               let uu____14387 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_14410 ->
                                         match uu___23_14410 with
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
                                              | uu____14424 -> false)
                                         | uu____14428 -> false)) in
                               (match uu____14387 with
                                | (bounds_probs, rest) ->
                                    let bounds_typs =
                                      let uu____14443 = whnf env this_rigid in
                                      let uu____14444 =
                                        FStar_List.collect
                                          (fun uu___24_14450 ->
                                             match uu___24_14450 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14456 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs in
                                                 [uu____14456]
                                             | uu____14460 -> [])
                                          bounds_probs in
                                      uu____14443 :: uu____14444 in
                                    let uu____14461 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl in
                                    (match uu____14461 with
                                     | (bound, sub_probs, wl1) ->
                                         let uu____14494 =
                                           let flex_u =
                                             flex_uvar_head this_flex in
                                           let bound1 =
                                             let uu____14509 =
                                               let uu____14510 =
                                                 FStar_Syntax_Subst.compress
                                                   bound in
                                               uu____14510.FStar_Syntax_Syntax.n in
                                             match uu____14509 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x, phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14522 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14522)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14533 -> bound in
                                           let uu____14534 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements") in
                                           (bound1, uu____14534) in
                                         (match uu____14494 with
                                          | (bound_typ, (eq_prob, wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14569 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel") in
                                                if uu____14569
                                                then
                                                  let wl'1 =
                                                    let uu___2089_14575 = wl1 in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2089_14575.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2089_14575.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2089_14575.ctr);
                                                      defer_ok =
                                                        (uu___2089_14575.defer_ok);
                                                      smt_ok =
                                                        (uu___2089_14575.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2089_14575.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2089_14575.tcenv);
                                                      wl_implicits =
                                                        (uu___2089_14575.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2089_14575.repr_subcomp_allowed)
                                                    } in
                                                  let uu____14576 =
                                                    wl_to_string wl'1 in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14576
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____14582 =
                                                  solve_t env eq_prob
                                                    (let uu___2094_14584 =
                                                       wl' in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2094_14584.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2094_14584.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2094_14584.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2094_14584.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2094_14584.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2094_14584.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2094_14584.repr_subcomp_allowed)
                                                     }) in
                                                match uu____14582 with
                                                | Success
                                                    (uu____14586,
                                                     defer_to_tac, imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2101_14590 =
                                                        wl' in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2101_14590.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2101_14590.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2101_14590.ctr);
                                                        defer_ok =
                                                          (uu___2101_14590.defer_ok);
                                                        smt_ok =
                                                          (uu___2101_14590.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2101_14590.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2101_14590.tcenv);
                                                        wl_implicits =
                                                          (uu___2101_14590.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2101_14590.repr_subcomp_allowed)
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
                                                    let uu____14607 =
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
                                                    ((let uu____14619 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu____14619
                                                      then
                                                        let uu____14624 =
                                                          let uu____14626 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs) in
                                                          FStar_All.pipe_right
                                                            uu____14626
                                                            (FStar_String.concat
                                                               "\n") in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14624
                                                      else ());
                                                     (let uu____14639 =
                                                        let uu____14654 =
                                                          base_and_refinement
                                                            env bound_typ in
                                                        (rank1, uu____14654) in
                                                      match uu____14639 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          uu____14676)) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14702 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____14702
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
                                                                  let uu____14722
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____14722))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          (x, phi))) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14747 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____14747
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
                                                                    let uu____14767
                                                                    =
                                                                    let uu____14772
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14772 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14767
                                                                    [] wl2 in
                                                                  let uu____14778
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____14778))))
                                                      | uu____14779 ->
                                                          let uu____14794 =
                                                            FStar_Thunk.map
                                                              (fun s ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg in
                                                          giveup env
                                                            uu____14794 p)))))))
                           | uu____14801 when flip ->
                               let uu____14802 =
                                 let uu____14804 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____14806 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14804 uu____14806 in
                               failwith uu____14802
                           | uu____14809 ->
                               let uu____14810 =
                                 let uu____14812 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____14814 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14812 uu____14814 in
                               failwith uu____14810)))))
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
                      (fun uu____14850 ->
                         match uu____14850 with
                         | (x, i) ->
                             let uu____14869 =
                               FStar_Syntax_Syntax.bv_to_name x in
                             (uu____14869, i)) bs_lhs in
                  let uu____14872 = lhs in
                  match uu____14872 with
                  | Flex (uu____14873, u_lhs, uu____14875) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14972 =
                            match uopt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14982 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos in
                                (uu____14982, univ) in
                          match uu____14972 with
                          | (k, univ) ->
                              let uu____14989 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2 in
                              (match uu____14989 with
                               | (uu____15006, u, wl3) ->
                                   let uu____15009 =
                                     f u (FStar_Pervasives_Native.Some univ) in
                                   (uu____15009, wl3)) in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____15035 =
                              let uu____15048 =
                                let uu____15059 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                uu____15059 ::
                                  (ct.FStar_Syntax_Syntax.effect_args) in
                              FStar_List.fold_right
                                (fun uu____15110 ->
                                   fun uu____15111 ->
                                     match (uu____15110, uu____15111) with
                                     | ((a, i), (out_args, wl2)) ->
                                         let uu____15212 =
                                           let uu____15219 =
                                             let uu____15222 =
                                               FStar_Syntax_Util.type_u () in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15222 in
                                           copy_uvar u_lhs [] uu____15219 wl2 in
                                         (match uu____15212 with
                                          | (uu____15251, t_a, wl3) ->
                                              let uu____15254 =
                                                copy_uvar u_lhs bs t_a wl3 in
                                              (match uu____15254 with
                                               | (uu____15273, a', wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____15048
                                ([], wl1) in
                            (match uu____15035 with
                             | (out_args, wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_15342 ->
                                        match uu___25_15342 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____15344 -> false
                                        | uu____15348 -> true) flags in
                                 let ct' =
                                   let uu___2220_15351 = ct in
                                   let uu____15352 =
                                     let uu____15355 = FStar_List.hd out_args in
                                     FStar_Pervasives_Native.fst uu____15355 in
                                   let uu____15370 = FStar_List.tl out_args in
                                   let uu____15387 =
                                     nodec ct.FStar_Syntax_Syntax.flags in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2220_15351.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2220_15351.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15352;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15370;
                                     FStar_Syntax_Syntax.flags = uu____15387
                                   } in
                                 ((let uu___2223_15391 = c in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2223_15391.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2223_15391.FStar_Syntax_Syntax.vars)
                                   }), wl2)) in
                      let uu____15394 =
                        FStar_Syntax_Util.arrow_formals_comp arrow in
                      (match uu____15394 with
                       | (formals, c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15432 =
                                   imitate_comp bs bs_terms c wl1 in
                                 (match uu____15432 with
                                  | (c', wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c' in
                                      let sol =
                                        let uu____15443 =
                                          let uu____15448 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____15448) in
                                        TERM uu____15443 in
                                      let uu____15449 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation" in
                                      (match uu____15449 with
                                       | (sub_prob, wl3) ->
                                           let uu____15463 =
                                             let uu____15464 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3 in
                                             attempt [sub_prob] uu____15464 in
                                           solve env uu____15463))
                             | (x, imp)::formals2 ->
                                 let uu____15486 =
                                   let uu____15493 =
                                     let uu____15496 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_right uu____15496
                                       FStar_Pervasives_Native.fst in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15493 wl1 in
                                 (match uu____15486 with
                                  | (_ctx_u_x, u_x, wl2) ->
                                      let y =
                                        let uu____15517 =
                                          let uu____15520 =
                                            FStar_Syntax_Syntax.range_of_bv x in
                                          FStar_Pervasives_Native.Some
                                            uu____15520 in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15517 u_x in
                                      let uu____15521 =
                                        let uu____15524 =
                                          let uu____15527 =
                                            let uu____15528 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y in
                                            (uu____15528, imp) in
                                          [uu____15527] in
                                        FStar_List.append bs_terms
                                          uu____15524 in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15521 formals2 wl2) in
                           let uu____15555 = occurs_check u_lhs arrow in
                           (match uu____15555 with
                            | (uu____15568, occurs_ok, msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15584 =
                                    mklstr
                                      (fun uu____15589 ->
                                         let uu____15590 =
                                           FStar_Option.get msg in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15590) in
                                  giveup_or_defer env orig wl uu____15584
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
              (let uu____15623 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____15623
               then
                 let uu____15628 =
                   FStar_Syntax_Print.binders_to_string ", " bs1 in
                 let uu____15631 =
                   FStar_Syntax_Print.binders_to_string ", " bs2 in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15628 (rel_to_string (p_rel orig)) uu____15631
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([], []) ->
                     let uu____15762 = rhs wl1 scope env1 subst in
                     (match uu____15762 with
                      | (rhs_prob, wl2) ->
                          ((let uu____15785 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel") in
                            if uu____15785
                            then
                              let uu____15790 = prob_to_string env1 rhs_prob in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15790
                            else ());
                           (let formula = p_guard rhs_prob in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1, imp)::xs1, (hd2, imp')::ys1) when
                     let uu____15868 = FStar_Syntax_Util.eq_aqual imp imp' in
                     uu____15868 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2293_15870 = hd1 in
                       let uu____15871 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2293_15870.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2293_15870.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15871
                       } in
                     let hd21 =
                       let uu___2296_15875 = hd2 in
                       let uu____15876 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2296_15875.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2296_15875.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15876
                       } in
                     let uu____15879 =
                       let uu____15884 =
                         FStar_All.pipe_left invert_rel (p_rel orig) in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15884
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter" in
                     (match uu____15879 with
                      | (prob, wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                          let subst1 =
                            let uu____15907 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15907 in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                          let uu____15914 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1 in
                          (match uu____15914 with
                           | (env3, FStar_Util.Inl (sub_probs, phi), wl3) ->
                               let phi1 =
                                 let uu____15986 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15986 in
                               ((let uu____16004 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel") in
                                 if uu____16004
                                 then
                                   let uu____16009 =
                                     FStar_Syntax_Print.term_to_string phi1 in
                                   let uu____16011 =
                                     FStar_Syntax_Print.bv_to_string hd12 in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____16009
                                     uu____16011
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____16046 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1) in
               let uu____16082 = aux wl [] env [] bs1 bs2 in
               match uu____16082 with
               | (env1, FStar_Util.Inr msg, wl1) -> giveup_lit env1 msg orig
               | (env1, FStar_Util.Inl (sub_probs, phi), wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1 in
                   let uu____16141 = attempt sub_probs wl2 in
                   solve env1 uu____16141)
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
            let uu___2334_16161 = wl in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2334_16161.wl_deferred_to_tac);
              ctr = (uu___2334_16161.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2334_16161.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2334_16161.repr_subcomp_allowed)
            } in
          let tx = FStar_Syntax_Unionfind.new_transaction () in
          let uu____16173 = try_solve env wl' in
          match uu____16173 with
          | Success (uu____16174, defer_to_tac, imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps in solve env wl1))
          | Failed (p, s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16187 = compress_tprob wl.tcenv problem in
         solve_t' env uu____16187 wl)
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
            let uu____16193 = should_defer_flex_to_user_tac env wl lhs in
            if uu____16193
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16206 =
                   FStar_List.map FStar_Pervasives_Native.fst bs in
                 FStar_Util.as_set uu____16206 FStar_Syntax_Syntax.order_bv in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16240 = lhs1 in
                 match uu____16240 with
                 | Flex (uu____16243, ctx_u, uu____16245) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16253 ->
                           let uu____16254 = sn_binders env1 bs in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16254 rhs1 in
                     [TERM (ctx_u, sol)] in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16303 = quasi_pattern env1 lhs1 in
                 match uu____16303 with
                 | FStar_Pervasives_Native.None ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs, uu____16337) ->
                     let uu____16342 = lhs1 in
                     (match uu____16342 with
                      | Flex (t_lhs, ctx_u, args) ->
                          let uu____16357 = occurs_check ctx_u rhs1 in
                          (match uu____16357 with
                           | (uvars, occurs_ok, msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16408 =
                                   let uu____16416 =
                                     let uu____16418 = FStar_Option.get msg in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16418 in
                                   FStar_Util.Inl uu____16416 in
                                 (uu____16408, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs) in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1 in
                                  let uu____16446 =
                                    let uu____16448 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs in
                                    Prims.op_Negation uu____16448 in
                                  if uu____16446
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16475 =
                                       let uu____16483 =
                                         mk_solution env1 lhs1 bs rhs1 in
                                       FStar_Util.Inr uu____16483 in
                                     let uu____16489 =
                                       restrict_all_uvars ctx_u uvars wl1 in
                                     (uu____16475, uu____16489))))) in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16533 = FStar_Syntax_Util.head_and_args rhs1 in
                 match uu____16533 with
                 | (rhs_hd, args) ->
                     let uu____16576 = FStar_Util.prefix args in
                     (match uu____16576 with
                      | (args_rhs, last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              rhs1.FStar_Syntax_Syntax.pos in
                          let uu____16646 = lhs1 in
                          (match uu____16646 with
                           | Flex (t_lhs, u_lhs, _lhs_args) ->
                               let uu____16650 =
                                 let uu____16661 =
                                   let uu____16668 =
                                     let uu____16671 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16671 in
                                   copy_uvar u_lhs [] uu____16668 wl1 in
                                 match uu____16661 with
                                 | (uu____16698, t_last_arg, wl2) ->
                                     let uu____16701 =
                                       let uu____16708 =
                                         let uu____16709 =
                                           let uu____16718 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg in
                                           [uu____16718] in
                                         FStar_List.append bs_lhs uu____16709 in
                                       copy_uvar u_lhs uu____16708 t_res_lhs
                                         wl2 in
                                     (match uu____16701 with
                                      | (uu____16753, lhs', wl3) ->
                                          let uu____16756 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3 in
                                          (match uu____16756 with
                                           | (uu____16773, lhs'_last_arg,
                                              wl4) ->
                                               (lhs', lhs'_last_arg, wl4))) in
                               (match uu____16650 with
                                | (lhs', lhs'_last_arg, wl2) ->
                                    let sol =
                                      let uu____16794 =
                                        let uu____16795 =
                                          let uu____16800 =
                                            let uu____16801 =
                                              let uu____16804 =
                                                let uu____16805 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    lhs'_last_arg in
                                                [uu____16805] in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                lhs' uu____16804
                                                t_lhs.FStar_Syntax_Syntax.pos in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16801
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____16800) in
                                        TERM uu____16795 in
                                      [uu____16794] in
                                    let uu____16830 =
                                      let uu____16837 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs" in
                                      match uu____16837 with
                                      | (p1, wl3) ->
                                          let uu____16857 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs" in
                                          (match uu____16857 with
                                           | (p2, wl4) -> ([p1; p2], wl4)) in
                                    (match uu____16830 with
                                     | (sub_probs, wl3) ->
                                         let uu____16889 =
                                           let uu____16890 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3 in
                                           attempt sub_probs uu____16890 in
                                         solve env1 uu____16889)))) in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16924 = FStar_Syntax_Util.head_and_args rhs2 in
                   match uu____16924 with
                   | (uu____16942, args) ->
                       (match args with | [] -> false | uu____16978 -> true) in
                 let is_arrow rhs2 =
                   let uu____16997 =
                     let uu____16998 = FStar_Syntax_Subst.compress rhs2 in
                     uu____16998.FStar_Syntax_Syntax.n in
                   match uu____16997 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____17002 -> true
                   | uu____17018 -> false in
                 let uu____17020 = quasi_pattern env1 lhs1 in
                 match uu____17020 with
                 | FStar_Pervasives_Native.None ->
                     let msg =
                       mklstr
                         (fun uu____17039 ->
                            let uu____17040 = prob_to_string env1 orig1 in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____17040) in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                     let uu____17049 = is_app rhs1 in
                     if uu____17049
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____17054 = is_arrow rhs1 in
                        if uu____17054
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu____17067 ->
                                  let uu____17068 = prob_to_string env1 orig1 in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____17068) in
                           giveup_or_defer env1 orig1 wl1 msg)) in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB ->
                   if wl.defer_ok
                   then
                     let uu____17072 = FStar_Thunk.mkv "flex-rigid subtyping" in
                     giveup_or_defer env orig wl uu____17072
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV ->
                   if wl.defer_ok
                   then
                     let uu____17078 = FStar_Thunk.mkv "flex-rigid subtyping" in
                     giveup_or_defer env orig wl uu____17078
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ ->
                   let uu____17083 = lhs in
                   (match uu____17083 with
                    | Flex (_t1, ctx_uv, args_lhs) ->
                        let uu____17087 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs in
                        (match uu____17087 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs in
                             let names_to_string1 fvs =
                               let uu____17105 =
                                 let uu____17109 =
                                   FStar_Util.set_elements fvs in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____17109 in
                               FStar_All.pipe_right uu____17105
                                 (FStar_String.concat ", ") in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders) in
                             let fvs2 = FStar_Syntax_Free.names rhs1 in
                             let uu____17130 = occurs_check ctx_uv rhs1 in
                             (match uu____17130 with
                              | (uvars, occurs_ok, msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17159 =
                                      let uu____17160 =
                                        let uu____17162 =
                                          FStar_Option.get msg in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17162 in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17160 in
                                    giveup_or_defer env orig wl uu____17159
                                  else
                                    (let uu____17170 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1 in
                                     if uu____17170
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1 in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars wl in
                                       let uu____17177 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1 in
                                       solve env uu____17177
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            mklstr
                                              (fun uu____17193 ->
                                                 let uu____17194 =
                                                   names_to_string1 fvs2 in
                                                 let uu____17196 =
                                                   names_to_string1 fvs1 in
                                                 let uu____17198 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders) in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17194 uu____17196
                                                   uu____17198) in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17210 ->
                             if wl.defer_ok
                             then
                               let uu____17214 =
                                 FStar_Thunk.mkv "Not a pattern" in
                               giveup_or_defer env orig wl uu____17214
                             else
                               (let uu____17219 =
                                  try_quasi_pattern orig env wl lhs rhs in
                                match uu____17219 with
                                | (FStar_Util.Inr sol, wl1) ->
                                    let uu____17245 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1 in
                                    solve env uu____17245
                                | (FStar_Util.Inl msg, uu____17247) ->
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
                  let uu____17265 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____17265
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV ->
                if wl.defer_ok
                then
                  let uu____17271 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____17271
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ ->
                let uu____17276 =
                  (should_defer_flex_to_user_tac env wl lhs) ||
                    (should_defer_flex_to_user_tac env wl rhs) in
                if uu____17276
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
                    (let uu____17283 =
                       FStar_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer env orig wl uu____17283)
                  else
                    (let uu____17288 =
                       let uu____17305 = quasi_pattern env lhs in
                       let uu____17312 = quasi_pattern env rhs in
                       (uu____17305, uu____17312) in
                     match uu____17288 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs, t_res_lhs),
                        FStar_Pervasives_Native.Some
                        (binders_rhs, t_res_rhs)) ->
                         let uu____17355 = lhs in
                         (match uu____17355 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17356;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17358;_},
                               u_lhs, uu____17360)
                              ->
                              let uu____17363 = rhs in
                              (match uu____17363 with
                               | Flex (uu____17364, u_rhs, uu____17366) ->
                                   let uu____17367 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs) in
                                   if uu____17367
                                   then
                                     let uu____17374 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl in
                                     solve env uu____17374
                                   else
                                     (let uu____17377 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders in
                                      match uu____17377 with
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
                                          let uu____17409 =
                                            let uu____17416 =
                                              let uu____17419 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17419 in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____17416
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
                                          (match uu____17409 with
                                           | (uu____17428, w, wl1) ->
                                               let w_app =
                                                 let uu____17432 =
                                                   FStar_List.map
                                                     (fun uu____17443 ->
                                                        match uu____17443
                                                        with
                                                        | (z, uu____17451) ->
                                                            let uu____17456 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____17456) zs in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____17432
                                                   w.FStar_Syntax_Syntax.pos in
                                               ((let uu____17458 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____17458
                                                 then
                                                   let uu____17463 =
                                                     let uu____17467 =
                                                       flex_t_to_string lhs in
                                                     let uu____17469 =
                                                       let uu____17473 =
                                                         flex_t_to_string rhs in
                                                       let uu____17475 =
                                                         let uu____17479 =
                                                           term_to_string w in
                                                         let uu____17481 =
                                                           let uu____17485 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs) in
                                                           let uu____17494 =
                                                             let uu____17498
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs) in
                                                             let uu____17507
                                                               =
                                                               let uu____17511
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs in
                                                               [uu____17511] in
                                                             uu____17498 ::
                                                               uu____17507 in
                                                           uu____17485 ::
                                                             uu____17494 in
                                                         uu____17479 ::
                                                           uu____17481 in
                                                       uu____17473 ::
                                                         uu____17475 in
                                                     uu____17467 ::
                                                       uu____17469 in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17463
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17528 =
                                                       let uu____17533 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs)) in
                                                       (u_lhs, uu____17533) in
                                                     TERM uu____17528 in
                                                   let uu____17534 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   if uu____17534
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17542 =
                                                          let uu____17547 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          (u_rhs,
                                                            uu____17547) in
                                                        TERM uu____17542 in
                                                      [s1; s2]) in
                                                 let uu____17548 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1 in
                                                 solve env uu____17548))))))
                     | uu____17549 ->
                         let uu____17566 =
                           FStar_Thunk.mkv "flex-flex: non-patterns" in
                         giveup_or_defer env orig wl uu____17566)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____17620 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu____17620
            then
              let uu____17625 = FStar_Syntax_Print.term_to_string t1 in
              let uu____17627 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____17629 = FStar_Syntax_Print.term_to_string t2 in
              let uu____17631 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17625 uu____17627 uu____17629 uu____17631
            else ());
           (let uu____17642 = FStar_Syntax_Util.head_and_args t1 in
            match uu____17642 with
            | (head1, args1) ->
                let uu____17685 = FStar_Syntax_Util.head_and_args t2 in
                (match uu____17685 with
                 | (head2, args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17755 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu____17755 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17760 =
                                defer_lit "universe constraints" orig wl3 in
                              k false uu____17760) in
                     let nargs = FStar_List.length args1 in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17781 =
                         mklstr
                           (fun uu____17792 ->
                              let uu____17793 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____17795 = args_to_string args1 in
                              let uu____17799 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu____17801 = args_to_string args2 in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17793 uu____17795 uu____17799
                                uu____17801) in
                       giveup env1 uu____17781 orig
                     else
                       (let uu____17808 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17813 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu____17813 = FStar_Syntax_Util.Equal) in
                        if uu____17808
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2607_17817 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2607_17817.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2607_17817.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2607_17817.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2607_17817.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2607_17817.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2607_17817.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2607_17817.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2607_17817.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu____17827 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu____17827
                                    else solve env1 wl2))
                        else
                          (let uu____17832 = base_and_refinement env1 t1 in
                           match uu____17832 with
                           | (base1, refinement1) ->
                               let uu____17857 = base_and_refinement env1 t2 in
                               (match uu____17857 with
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
                                           let uu____18022 =
                                             FStar_List.fold_right
                                               (fun uu____18062 ->
                                                  fun uu____18063 ->
                                                    match (uu____18062,
                                                            uu____18063)
                                                    with
                                                    | (((a1, uu____18115),
                                                        (a2, uu____18117)),
                                                       (probs, wl3)) ->
                                                        let uu____18166 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu____18166
                                                         with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu____18022 with
                                           | (subprobs, wl3) ->
                                               ((let uu____18209 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____18209
                                                 then
                                                   let uu____18214 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18214
                                                 else ());
                                                (let uu____18220 =
                                                   FStar_Options.defensive () in
                                                 if uu____18220
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
                                                    (let uu____18247 =
                                                       mk_sub_probs wl3 in
                                                     match uu____18247 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu____18263 =
                                                             FStar_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18263 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu____18271 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2
                                                           uu____18271)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu____18296 =
                                                    mk_sub_probs wl3 in
                                                  match uu____18296 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu____18312 =
                                                          FStar_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18312 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu____18320 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu____18320) in
                                         let unfold_and_retry d env2 wl2
                                           uu____18348 =
                                           match uu____18348 with
                                           | (prob, reason) ->
                                               ((let uu____18365 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____18365
                                                 then
                                                   let uu____18370 =
                                                     prob_to_string env2 orig in
                                                   let uu____18372 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____18370 uu____18372
                                                 else ());
                                                (let uu____18378 =
                                                   let uu____18387 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu____18390 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu____18387, uu____18390) in
                                                 match uu____18378 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18403 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu____18403 with
                                                      | (head1', uu____18421)
                                                          ->
                                                          let uu____18446 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu____18446
                                                           with
                                                           | (head2',
                                                              uu____18464) ->
                                                               let uu____18489
                                                                 =
                                                                 let uu____18494
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu____18495
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu____18494,
                                                                   uu____18495) in
                                                               (match uu____18489
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
                                                                    let uu____18497
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____18497
                                                                    then
                                                                    let uu____18502
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____18504
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu____18506
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____18508
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18502
                                                                    uu____18504
                                                                    uu____18506
                                                                    uu____18508
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18513
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2695_18521
                                                                    = torig in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2695_18521.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2695_18521.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2695_18521.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2695_18521.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2695_18521.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2695_18521.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2695_18521.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2695_18521.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
                                                                    let uu____18523
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____18523
                                                                    then
                                                                    let uu____18528
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18528
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18533 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu____18545 =
                                             delta_depth_of_term env1 head1 in
                                           match uu____18545 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d in
                                         let treat_as_injective =
                                           let uu____18553 =
                                             let uu____18554 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu____18554.FStar_Syntax_Syntax.n in
                                           match uu____18553 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18559 -> false in
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
                                          | uu____18562 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18565 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t env1
                                           (let uu___2715_18601 = problem in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2715_18601.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2715_18601.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2715_18601.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2715_18601.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2715_18601.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2715_18601.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2715_18601.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2715_18601.FStar_TypeChecker_Common.rank)
                                            }) wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18677 = destruct_flex_t scrutinee wl1 in
             match uu____18677 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu____18688 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p in
                 (match uu____18688 with
                  | (xs, pat_term, uu____18704, uu____18705) ->
                      let uu____18710 =
                        FStar_List.fold_left
                          (fun uu____18733 ->
                             fun x ->
                               match uu____18733 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____18754 = copy_uvar uv [] t_x wl3 in
                                   (match uu____18754 with
                                    | (uu____18773, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu____18710 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu____18794 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic" in
                           (match uu____18794 with
                            | (prob, wl4) ->
                                let wl' =
                                  let uu___2756_18811 = wl4 in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2756_18811.wl_deferred_to_tac);
                                    ctr = (uu___2756_18811.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2756_18811.umax_heuristic_ok);
                                    tcenv = (uu___2756_18811.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2756_18811.repr_subcomp_allowed)
                                  } in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let uu____18822 = solve env1 wl' in
                                (match uu____18822 with
                                 | Success (uu____18825, defer_to_tac, imps)
                                     ->
                                     let wl'1 =
                                       let uu___2765_18829 = wl' in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2765_18829.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2765_18829.wl_deferred_to_tac);
                                         ctr = (uu___2765_18829.ctr);
                                         defer_ok =
                                           (uu___2765_18829.defer_ok);
                                         smt_ok = (uu___2765_18829.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2765_18829.umax_heuristic_ok);
                                         tcenv = (uu___2765_18829.tcenv);
                                         wl_implicits =
                                           (uu___2765_18829.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2765_18829.repr_subcomp_allowed)
                                       } in
                                     let uu____18830 = solve env1 wl'1 in
                                     (match uu____18830 with
                                      | Success
                                          (uu____18833, defer_to_tac', imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18837 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps') in
                                            FStar_Pervasives_Native.Some
                                              uu____18837))
                                      | Failed uu____18843 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18849 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None))))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu____18872 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu____18872
                 then
                   let uu____18877 = FStar_Syntax_Print.term_to_string t1 in
                   let uu____18879 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18877 uu____18879
                 else ());
                (let uu____18884 =
                   let uu____18905 =
                     let uu____18914 = FStar_Syntax_Util.unmeta t1 in
                     (s1, uu____18914) in
                   let uu____18921 =
                     let uu____18930 = FStar_Syntax_Util.unmeta t2 in
                     (s2, uu____18930) in
                   (uu____18905, uu____18921) in
                 match uu____18884 with
                 | ((uu____18960,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____18963;
                       FStar_Syntax_Syntax.vars = uu____18964;_}),
                    (s, t)) ->
                     let uu____19035 =
                       let uu____19037 = is_flex scrutinee in
                       Prims.op_Negation uu____19037 in
                     if uu____19035
                     then
                       ((let uu____19048 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____19048
                         then
                           let uu____19053 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19053
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19072 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19072
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19087 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19087
                           then
                             let uu____19092 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____19094 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19092 uu____19094
                           else ());
                          (let pat_discriminates uu___26_19119 =
                             match uu___26_19119 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19135;
                                  FStar_Syntax_Syntax.p = uu____19136;_},
                                FStar_Pervasives_Native.None, uu____19137) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19151;
                                  FStar_Syntax_Syntax.p = uu____19152;_},
                                FStar_Pervasives_Native.None, uu____19153) ->
                                 true
                             | uu____19180 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____19283 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____19283 with
                                       | (uu____19285, uu____19286, t') ->
                                           let uu____19304 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____19304 with
                                            | (FullMatch, uu____19316) ->
                                                true
                                            | (HeadMatch uu____19330,
                                               uu____19331) -> true
                                            | uu____19346 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____19383 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____19383
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19394 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____19394 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____19482, uu____19483)
                                       -> branches1
                                   | uu____19628 -> branches in
                                 let uu____19683 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____19692 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____19692 with
                                        | (p, uu____19696, uu____19697) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____19726 ->
                                      FStar_Util.Inr uu____19726) uu____19683))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19756 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____19756 with
                                | (p, uu____19765, e) ->
                                    ((let uu____19784 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____19784
                                      then
                                        let uu____19789 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____19791 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19789 uu____19791
                                      else ());
                                     (let uu____19796 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____19811 ->
                                           FStar_Util.Inr uu____19811)
                                        uu____19796)))))
                 | ((s, t),
                    (uu____19814,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____19817;
                       FStar_Syntax_Syntax.vars = uu____19818;_}))
                     ->
                     let uu____19887 =
                       let uu____19889 = is_flex scrutinee in
                       Prims.op_Negation uu____19889 in
                     if uu____19887
                     then
                       ((let uu____19900 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____19900
                         then
                           let uu____19905 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19905
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19924 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19924
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19939 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19939
                           then
                             let uu____19944 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____19946 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19944 uu____19946
                           else ());
                          (let pat_discriminates uu___26_19971 =
                             match uu___26_19971 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19987;
                                  FStar_Syntax_Syntax.p = uu____19988;_},
                                FStar_Pervasives_Native.None, uu____19989) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____20003;
                                  FStar_Syntax_Syntax.p = uu____20004;_},
                                FStar_Pervasives_Native.None, uu____20005) ->
                                 true
                             | uu____20032 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____20135 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____20135 with
                                       | (uu____20137, uu____20138, t') ->
                                           let uu____20156 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____20156 with
                                            | (FullMatch, uu____20168) ->
                                                true
                                            | (HeadMatch uu____20182,
                                               uu____20183) -> true
                                            | uu____20198 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____20235 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____20235
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20246 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____20246 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____20334, uu____20335)
                                       -> branches1
                                   | uu____20480 -> branches in
                                 let uu____20535 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____20544 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____20544 with
                                        | (p, uu____20548, uu____20549) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____20578 ->
                                      FStar_Util.Inr uu____20578) uu____20535))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20608 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____20608 with
                                | (p, uu____20617, e) ->
                                    ((let uu____20636 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____20636
                                      then
                                        let uu____20641 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____20643 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20641 uu____20643
                                      else ());
                                     (let uu____20648 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____20663 ->
                                           FStar_Util.Inr uu____20663)
                                        uu____20648)))))
                 | uu____20664 ->
                     ((let uu____20686 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu____20686
                       then
                         let uu____20691 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____20693 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20691 uu____20693
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____20739 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu____20739
            then
              let uu____20744 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____20746 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____20748 = FStar_Syntax_Print.term_to_string t1 in
              let uu____20750 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20744 uu____20746 uu____20748 uu____20750
            else ());
           (let uu____20755 = head_matches_delta env1 wl1 t1 t2 in
            match uu____20755 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu____20786, uu____20787) ->
                     let rec may_relate head =
                       let uu____20815 =
                         let uu____20816 = FStar_Syntax_Subst.compress head in
                         uu____20816.FStar_Syntax_Syntax.n in
                       match uu____20815 with
                       | FStar_Syntax_Syntax.Tm_name uu____20820 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20822 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20847 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv in
                           (match uu____20847 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20849 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20852
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20853 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t, uu____20856, uu____20857) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t, uu____20899) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t, uu____20905) ->
                           may_relate t
                       | uu____20910 -> false in
                     let uu____20912 =
                       try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu____20912 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20925 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig uu____20925
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None) ->
                          let uu____20935 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok in
                          if uu____20935
                          then
                            let uu____20938 =
                              guard_of_prob env1 wl1 problem t1 t2 in
                            (match uu____20938 with
                             | (guard, wl2) ->
                                 let uu____20945 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2 in
                                 solve env1 uu____20945)
                          else
                            (let uu____20948 =
                               mklstr
                                 (fun uu____20959 ->
                                    let uu____20960 =
                                      FStar_Syntax_Print.term_to_string head1 in
                                    let uu____20962 =
                                      let uu____20964 =
                                        let uu____20968 =
                                          delta_depth_of_term env1 head1 in
                                        FStar_Util.bind_opt uu____20968
                                          (fun x ->
                                             let uu____20975 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____20975) in
                                      FStar_Util.dflt "" uu____20964 in
                                    let uu____20980 =
                                      FStar_Syntax_Print.term_to_string head2 in
                                    let uu____20982 =
                                      let uu____20984 =
                                        let uu____20988 =
                                          delta_depth_of_term env1 head2 in
                                        FStar_Util.bind_opt uu____20988
                                          (fun x ->
                                             let uu____20995 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____20995) in
                                      FStar_Util.dflt "" uu____20984 in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20960 uu____20962 uu____20980
                                      uu____20982) in
                             giveup env1 uu____20948 orig))
                 | (HeadMatch (true), uu____21001) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____21016 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu____21016 with
                        | (guard, wl2) ->
                            let uu____21023 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu____21023)
                     else
                       (let uu____21026 =
                          mklstr
                            (fun uu____21033 ->
                               let uu____21034 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____21036 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____21034 uu____21036) in
                        giveup env1 uu____21026 orig)
                 | (uu____21039, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       (let uu___2947_21053 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2947_21053.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2947_21053.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2947_21053.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2947_21053.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2947_21053.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2947_21053.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2947_21053.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2947_21053.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____21080 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____21080
          then
            let uu____21083 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____21083
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu____21089 =
                let uu____21092 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____21092 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____21089 t1);
             (let uu____21111 =
                let uu____21114 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____21114 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____21111 t2);
             (let uu____21133 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu____21133
              then
                let uu____21137 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu____21139 =
                  let uu____21141 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu____21143 =
                    let uu____21145 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu____21145 in
                  Prims.op_Hat uu____21141 uu____21143 in
                let uu____21148 =
                  let uu____21150 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu____21152 =
                    let uu____21154 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu____21154 in
                  Prims.op_Hat uu____21150 uu____21152 in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21137 uu____21139 uu____21148
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21161, uu____21162) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21178, FStar_Syntax_Syntax.Tm_delayed uu____21179) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21195, uu____21196) ->
                  let uu____21223 =
                    let uu___2978_21224 = problem in
                    let uu____21225 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2978_21224.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21225;
                      FStar_TypeChecker_Common.relation =
                        (uu___2978_21224.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2978_21224.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2978_21224.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2978_21224.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2978_21224.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2978_21224.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2978_21224.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2978_21224.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21223 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21226, uu____21227) ->
                  let uu____21234 =
                    let uu___2984_21235 = problem in
                    let uu____21236 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2984_21235.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21236;
                      FStar_TypeChecker_Common.relation =
                        (uu___2984_21235.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2984_21235.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2984_21235.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2984_21235.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2984_21235.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2984_21235.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2984_21235.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2984_21235.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21234 wl
              | (uu____21237, FStar_Syntax_Syntax.Tm_ascribed uu____21238) ->
                  let uu____21265 =
                    let uu___2990_21266 = problem in
                    let uu____21267 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2990_21266.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2990_21266.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2990_21266.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21267;
                      FStar_TypeChecker_Common.element =
                        (uu___2990_21266.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2990_21266.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2990_21266.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2990_21266.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2990_21266.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2990_21266.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21265 wl
              | (uu____21268, FStar_Syntax_Syntax.Tm_meta uu____21269) ->
                  let uu____21276 =
                    let uu___2996_21277 = problem in
                    let uu____21278 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2996_21277.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2996_21277.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2996_21277.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21278;
                      FStar_TypeChecker_Common.element =
                        (uu___2996_21277.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2996_21277.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2996_21277.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2996_21277.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2996_21277.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2996_21277.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21276 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____21280),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu____21282)) ->
                  let uu____21291 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu____21291
              | (FStar_Syntax_Syntax.Tm_bvar uu____21292, uu____21293) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21295, FStar_Syntax_Syntax.Tm_bvar uu____21296) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___27_21366 =
                    match uu___27_21366 with
                    | [] -> c
                    | bs ->
                        let uu____21394 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu____21394 in
                  let uu____21405 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu____21405 with
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
                                    let uu____21554 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu____21554
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___28_21643 =
                    match uu___28_21643 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu____21685 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu____21685 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu____21830 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu____21831 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu____21830
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21831 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21833, uu____21834) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21865 -> true
                    | uu____21885 -> false in
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
                      (let uu____21945 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3098_21953 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3098_21953.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3098_21953.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3098_21953.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3098_21953.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3098_21953.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3098_21953.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3098_21953.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3098_21953.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3098_21953.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3098_21953.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3098_21953.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3098_21953.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3098_21953.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3098_21953.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3098_21953.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3098_21953.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3098_21953.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3098_21953.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3098_21953.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3098_21953.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3098_21953.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3098_21953.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3098_21953.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3098_21953.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3098_21953.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3098_21953.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3098_21953.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3098_21953.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3098_21953.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3098_21953.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3098_21953.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3098_21953.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3098_21953.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3098_21953.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3098_21953.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3098_21953.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3098_21953.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3098_21953.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3098_21953.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3098_21953.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3098_21953.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3098_21953.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3098_21953.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3098_21953.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____21945 with
                       | (uu____21958, ty, uu____21960) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____21969 =
                                 let uu____21970 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____21970.FStar_Syntax_Syntax.n in
                               match uu____21969 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21973 ->
                                   let uu____21980 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____21980
                               | uu____21981 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____21984 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____21984
                             then
                               let uu____21989 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____21991 =
                                 let uu____21993 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21993 in
                               let uu____21994 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21989 uu____21991 uu____21994
                             else ());
                            r1)) in
                  let uu____21999 =
                    let uu____22016 = maybe_eta t1 in
                    let uu____22023 = maybe_eta t2 in
                    (uu____22016, uu____22023) in
                  (match uu____21999 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3119_22065 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3119_22065.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3119_22065.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3119_22065.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3119_22065.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3119_22065.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3119_22065.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3119_22065.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3119_22065.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____22086 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22086
                       then
                         let uu____22089 = destruct_flex_t not_abs wl in
                         (match uu____22089 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_22106 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_22106.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_22106.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_22106.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_22106.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_22106.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_22106.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_22106.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_22106.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22109 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22109 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____22132 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22132
                       then
                         let uu____22135 = destruct_flex_t not_abs wl in
                         (match uu____22135 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_22152 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_22152.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_22152.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_22152.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_22152.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_22152.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_22152.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_22152.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_22152.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22155 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22155 orig))
                   | uu____22158 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22176, FStar_Syntax_Syntax.Tm_abs uu____22177) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22208 -> true
                    | uu____22228 -> false in
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
                      (let uu____22288 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3098_22296 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3098_22296.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3098_22296.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3098_22296.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3098_22296.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3098_22296.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3098_22296.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3098_22296.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3098_22296.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3098_22296.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3098_22296.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3098_22296.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3098_22296.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3098_22296.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3098_22296.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3098_22296.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3098_22296.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3098_22296.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3098_22296.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3098_22296.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3098_22296.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3098_22296.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3098_22296.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3098_22296.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3098_22296.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3098_22296.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3098_22296.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3098_22296.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3098_22296.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3098_22296.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3098_22296.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3098_22296.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3098_22296.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3098_22296.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3098_22296.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3098_22296.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3098_22296.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3098_22296.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3098_22296.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3098_22296.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3098_22296.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3098_22296.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3098_22296.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3098_22296.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3098_22296.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____22288 with
                       | (uu____22301, ty, uu____22303) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____22312 =
                                 let uu____22313 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____22313.FStar_Syntax_Syntax.n in
                               match uu____22312 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22316 ->
                                   let uu____22323 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____22323
                               | uu____22324 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____22327 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____22327
                             then
                               let uu____22332 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____22334 =
                                 let uu____22336 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22336 in
                               let uu____22337 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22332 uu____22334 uu____22337
                             else ());
                            r1)) in
                  let uu____22342 =
                    let uu____22359 = maybe_eta t1 in
                    let uu____22366 = maybe_eta t2 in
                    (uu____22359, uu____22366) in
                  (match uu____22342 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3119_22408 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3119_22408.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3119_22408.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3119_22408.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3119_22408.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3119_22408.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3119_22408.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3119_22408.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3119_22408.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____22429 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22429
                       then
                         let uu____22432 = destruct_flex_t not_abs wl in
                         (match uu____22432 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_22449 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_22449.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_22449.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_22449.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_22449.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_22449.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_22449.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_22449.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_22449.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22452 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22452 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____22475 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22475
                       then
                         let uu____22478 = destruct_flex_t not_abs wl in
                         (match uu____22478 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3136_22495 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3136_22495.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3136_22495.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3136_22495.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3136_22495.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3136_22495.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3136_22495.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3136_22495.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3136_22495.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22498 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22498 orig))
                   | uu____22501 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu____22531 =
                    let uu____22536 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu____22536 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ((let uu___3159_22564 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3159_22564.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3159_22564.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3161_22566 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3161_22566.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3161_22566.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22567, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ((let uu___3159_22582 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3159_22582.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3159_22582.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3161_22584 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3161_22584.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3161_22584.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22585 -> (x1, x2) in
                  (match uu____22531 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu____22604 = as_refinement false env t11 in
                       (match uu____22604 with
                        | (x12, phi11) ->
                            let uu____22612 = as_refinement false env t21 in
                            (match uu____22612 with
                             | (x22, phi21) ->
                                 ((let uu____22621 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu____22621
                                   then
                                     ((let uu____22626 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu____22628 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu____22630 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22626
                                         uu____22628 uu____22630);
                                      (let uu____22633 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu____22635 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu____22637 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22633
                                         uu____22635 uu____22637))
                                   else ());
                                  (let uu____22642 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu____22642 with
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
                                         let uu____22713 = imp phi13 phi23 in
                                         FStar_All.pipe_right uu____22713
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu____22725 =
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
                                         (let uu____22738 =
                                            let uu____22741 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22741 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22738
                                            (p_guard base_prob));
                                         (let uu____22760 =
                                            let uu____22763 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22763 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22760
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu____22782 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu____22782) in
                                       let has_uvars =
                                         (let uu____22787 =
                                            let uu____22789 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Util.set_is_empty
                                              uu____22789 in
                                          Prims.op_Negation uu____22787) ||
                                           (let uu____22793 =
                                              let uu____22795 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Util.set_is_empty
                                                uu____22795 in
                                            Prims.op_Negation uu____22793) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22799 =
                                           let uu____22804 =
                                             let uu____22813 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu____22813] in
                                           mk_t_problem wl1 uu____22804 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu____22799 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu____22836 =
                                                solve env1
                                                  (let uu___3204_22838 = wl2 in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3204_22838.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3204_22838.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3204_22838.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3204_22838.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3204_22838.tcenv);
                                                     wl_implicits =
                                                       (uu___3204_22838.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3204_22838.repr_subcomp_allowed)
                                                   }) in
                                              (match uu____22836 with
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
                                                   (uu____22853,
                                                    defer_to_tac,
                                                    uu____22855)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22860 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22860 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       let uu___3220_22869 =
                                                         wl3 in
                                                       {
                                                         attempting =
                                                           (uu___3220_22869.attempting);
                                                         wl_deferred =
                                                           (uu___3220_22869.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3220_22869.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3220_22869.defer_ok);
                                                         smt_ok =
                                                           (uu___3220_22869.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3220_22869.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3220_22869.tcenv);
                                                         wl_implicits =
                                                           (uu___3220_22869.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3220_22869.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac [] in
                                                     let uu____22872 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu____22872))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22875,
                 FStar_Syntax_Syntax.Tm_uvar uu____22876) ->
                  let uu____22901 = ensure_no_uvar_subst t1 wl in
                  (match uu____22901 with
                   | (t11, wl1) ->
                       let uu____22908 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____22908 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22917;
                    FStar_Syntax_Syntax.pos = uu____22918;
                    FStar_Syntax_Syntax.vars = uu____22919;_},
                  uu____22920),
                 FStar_Syntax_Syntax.Tm_uvar uu____22921) ->
                  let uu____22970 = ensure_no_uvar_subst t1 wl in
                  (match uu____22970 with
                   | (t11, wl1) ->
                       let uu____22977 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____22977 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22986,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22987;
                    FStar_Syntax_Syntax.pos = uu____22988;
                    FStar_Syntax_Syntax.vars = uu____22989;_},
                  uu____22990)) ->
                  let uu____23039 = ensure_no_uvar_subst t1 wl in
                  (match uu____23039 with
                   | (t11, wl1) ->
                       let uu____23046 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____23046 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23055;
                    FStar_Syntax_Syntax.pos = uu____23056;
                    FStar_Syntax_Syntax.vars = uu____23057;_},
                  uu____23058),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23059;
                    FStar_Syntax_Syntax.pos = uu____23060;
                    FStar_Syntax_Syntax.vars = uu____23061;_},
                  uu____23062)) ->
                  let uu____23135 = ensure_no_uvar_subst t1 wl in
                  (match uu____23135 with
                   | (t11, wl1) ->
                       let uu____23142 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____23142 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23151, uu____23152) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23165 = destruct_flex_t t1 wl in
                  (match uu____23165 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23172;
                    FStar_Syntax_Syntax.pos = uu____23173;
                    FStar_Syntax_Syntax.vars = uu____23174;_},
                  uu____23175),
                 uu____23176) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23213 = destruct_flex_t t1 wl in
                  (match uu____23213 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23220, FStar_Syntax_Syntax.Tm_uvar uu____23221) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23234, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23235;
                    FStar_Syntax_Syntax.pos = uu____23236;
                    FStar_Syntax_Syntax.vars = uu____23237;_},
                  uu____23238)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____23275,
                 FStar_Syntax_Syntax.Tm_arrow uu____23276) ->
                  solve_t' env
                    (let uu___3323_23304 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3323_23304.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3323_23304.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3323_23304.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3323_23304.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3323_23304.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3323_23304.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3323_23304.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3323_23304.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3323_23304.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23305;
                    FStar_Syntax_Syntax.pos = uu____23306;
                    FStar_Syntax_Syntax.vars = uu____23307;_},
                  uu____23308),
                 FStar_Syntax_Syntax.Tm_arrow uu____23309) ->
                  solve_t' env
                    (let uu___3323_23361 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3323_23361.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3323_23361.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3323_23361.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3323_23361.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3323_23361.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3323_23361.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3323_23361.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3323_23361.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3323_23361.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23362, FStar_Syntax_Syntax.Tm_uvar uu____23363) ->
                  let uu____23376 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23376
              | (uu____23377, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23378;
                    FStar_Syntax_Syntax.pos = uu____23379;
                    FStar_Syntax_Syntax.vars = uu____23380;_},
                  uu____23381)) ->
                  let uu____23418 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23418
              | (FStar_Syntax_Syntax.Tm_uvar uu____23419, uu____23420) ->
                  let uu____23433 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23433
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23434;
                    FStar_Syntax_Syntax.pos = uu____23435;
                    FStar_Syntax_Syntax.vars = uu____23436;_},
                  uu____23437),
                 uu____23438) ->
                  let uu____23475 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23475
              | (FStar_Syntax_Syntax.Tm_refine uu____23476, uu____23477) ->
                  let t21 =
                    let uu____23485 = base_and_refinement env t2 in
                    FStar_All.pipe_left force_refinement uu____23485 in
                  solve_t env
                    (let uu___3358_23511 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3358_23511.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3358_23511.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3358_23511.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3358_23511.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3358_23511.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3358_23511.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3358_23511.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3358_23511.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3358_23511.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23512, FStar_Syntax_Syntax.Tm_refine uu____23513) ->
                  let t11 =
                    let uu____23521 = base_and_refinement env t1 in
                    FStar_All.pipe_left force_refinement uu____23521 in
                  solve_t env
                    (let uu___3365_23547 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3365_23547.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3365_23547.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3365_23547.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3365_23547.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3365_23547.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3365_23547.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3365_23547.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3365_23547.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3365_23547.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match (s1, brs1),
                 FStar_Syntax_Syntax.Tm_match (s2, brs2)) ->
                  let by_smt uu____23629 =
                    let uu____23630 = guard_of_prob env wl problem t1 t2 in
                    match uu____23630 with
                    | (guard, wl1) ->
                        let uu____23637 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu____23637 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu____23856 = br1 in
                        (match uu____23856 with
                         | (p1, w1, uu____23885) ->
                             let uu____23902 = br2 in
                             (match uu____23902 with
                              | (p2, w2, uu____23925) ->
                                  let uu____23930 =
                                    let uu____23932 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu____23932 in
                                  if uu____23930
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23959 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu____23959 with
                                     | ((p11, w11, e1), s) ->
                                         let uu____23996 = br2 in
                                         (match uu____23996 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu____24029 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____24029 in
                                              let uu____24034 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____24065,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu____24086) ->
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
                                                    let uu____24145 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu____24145 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Util.bind_opt uu____24034
                                                (fun uu____24217 ->
                                                   match uu____24217 with
                                                   | (wprobs, wl2) ->
                                                       let uu____24254 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu____24254
                                                        with
                                                        | (prob, wl3) ->
                                                            ((let uu____24275
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu____24275
                                                              then
                                                                let uu____24280
                                                                  =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu____24282
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24280
                                                                  uu____24282
                                                              else ());
                                                             (let uu____24288
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Util.bind_opt
                                                                uu____24288
                                                                (fun
                                                                   uu____24324
                                                                   ->
                                                                   match uu____24324
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
                    | uu____24453 -> FStar_Pervasives_Native.None in
                  let uu____24494 = solve_branches wl brs1 brs2 in
                  (match uu____24494 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24520 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu____24520 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu____24547 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu____24547 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu____24581 =
                                FStar_List.map
                                  (fun uu____24593 ->
                                     match uu____24593 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu____24581 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu____24602 =
                              let uu____24603 =
                                let uu____24604 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1 in
                                attempt uu____24604
                                  (let uu___3464_24612 = wl3 in
                                   {
                                     attempting =
                                       (uu___3464_24612.attempting);
                                     wl_deferred =
                                       (uu___3464_24612.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3464_24612.wl_deferred_to_tac);
                                     ctr = (uu___3464_24612.ctr);
                                     defer_ok = (uu___3464_24612.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3464_24612.umax_heuristic_ok);
                                     tcenv = (uu___3464_24612.tcenv);
                                     wl_implicits =
                                       (uu___3464_24612.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3464_24612.repr_subcomp_allowed)
                                   }) in
                              solve env uu____24603 in
                            (match uu____24602 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24618 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24627 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu____24627 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24630, uu____24631) ->
                  let head1 =
                    let uu____24655 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24655
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24701 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24701
                      FStar_Pervasives_Native.fst in
                  ((let uu____24747 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24747
                    then
                      let uu____24751 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24753 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24755 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24751 uu____24753 uu____24755
                    else ());
                   (let no_free_uvars t =
                      (let uu____24769 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24769) &&
                        (let uu____24773 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24773) in
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
                      let uu____24792 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24792 = FStar_Syntax_Util.Equal in
                    let uu____24793 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24793
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24797 = equal t1 t2 in
                         (if uu____24797
                          then
                            let uu____24800 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24800
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24805 =
                            let uu____24812 = equal t1 t2 in
                            if uu____24812
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24825 = mk_eq2 wl env orig t1 t2 in
                               match uu____24825 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24805 with
                          | (guard, wl1) ->
                              let uu____24846 = solve_prob orig guard [] wl1 in
                              solve env uu____24846))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24849, uu____24850) ->
                  let head1 =
                    let uu____24858 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24858
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24904 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24904
                      FStar_Pervasives_Native.fst in
                  ((let uu____24950 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24950
                    then
                      let uu____24954 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24956 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24958 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24954 uu____24956 uu____24958
                    else ());
                   (let no_free_uvars t =
                      (let uu____24972 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24972) &&
                        (let uu____24976 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24976) in
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
                      let uu____24995 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24995 = FStar_Syntax_Util.Equal in
                    let uu____24996 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24996
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25000 = equal t1 t2 in
                         (if uu____25000
                          then
                            let uu____25003 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25003
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25008 =
                            let uu____25015 = equal t1 t2 in
                            if uu____25015
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25028 = mk_eq2 wl env orig t1 t2 in
                               match uu____25028 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25008 with
                          | (guard, wl1) ->
                              let uu____25049 = solve_prob orig guard [] wl1 in
                              solve env uu____25049))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____25052, uu____25053) ->
                  let head1 =
                    let uu____25055 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25055
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25101 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25101
                      FStar_Pervasives_Native.fst in
                  ((let uu____25147 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25147
                    then
                      let uu____25151 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25153 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25155 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25151 uu____25153 uu____25155
                    else ());
                   (let no_free_uvars t =
                      (let uu____25169 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25169) &&
                        (let uu____25173 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25173) in
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
                      let uu____25192 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25192 = FStar_Syntax_Util.Equal in
                    let uu____25193 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25193
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25197 = equal t1 t2 in
                         (if uu____25197
                          then
                            let uu____25200 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25200
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25205 =
                            let uu____25212 = equal t1 t2 in
                            if uu____25212
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25225 = mk_eq2 wl env orig t1 t2 in
                               match uu____25225 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25205 with
                          | (guard, wl1) ->
                              let uu____25246 = solve_prob orig guard [] wl1 in
                              solve env uu____25246))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25249, uu____25250) ->
                  let head1 =
                    let uu____25252 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25252
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25298 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25298
                      FStar_Pervasives_Native.fst in
                  ((let uu____25344 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25344
                    then
                      let uu____25348 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25350 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25352 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25348 uu____25350 uu____25352
                    else ());
                   (let no_free_uvars t =
                      (let uu____25366 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25366) &&
                        (let uu____25370 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25370) in
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
                      let uu____25389 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25389 = FStar_Syntax_Util.Equal in
                    let uu____25390 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25390
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25394 = equal t1 t2 in
                         (if uu____25394
                          then
                            let uu____25397 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25397
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25402 =
                            let uu____25409 = equal t1 t2 in
                            if uu____25409
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25422 = mk_eq2 wl env orig t1 t2 in
                               match uu____25422 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25402 with
                          | (guard, wl1) ->
                              let uu____25443 = solve_prob orig guard [] wl1 in
                              solve env uu____25443))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25446, uu____25447) ->
                  let head1 =
                    let uu____25449 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25449
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25489 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25489
                      FStar_Pervasives_Native.fst in
                  ((let uu____25529 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25529
                    then
                      let uu____25533 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25535 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25537 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25533 uu____25535 uu____25537
                    else ());
                   (let no_free_uvars t =
                      (let uu____25551 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25551) &&
                        (let uu____25555 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25555) in
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
                      let uu____25574 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25574 = FStar_Syntax_Util.Equal in
                    let uu____25575 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25575
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25579 = equal t1 t2 in
                         (if uu____25579
                          then
                            let uu____25582 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25582
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25587 =
                            let uu____25594 = equal t1 t2 in
                            if uu____25594
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25607 = mk_eq2 wl env orig t1 t2 in
                               match uu____25607 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25587 with
                          | (guard, wl1) ->
                              let uu____25628 = solve_prob orig guard [] wl1 in
                              solve env uu____25628))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25631, uu____25632) ->
                  let head1 =
                    let uu____25650 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25650
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25690 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25690
                      FStar_Pervasives_Native.fst in
                  ((let uu____25730 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25730
                    then
                      let uu____25734 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25736 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25738 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25734 uu____25736 uu____25738
                    else ());
                   (let no_free_uvars t =
                      (let uu____25752 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25752) &&
                        (let uu____25756 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25756) in
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
                      let uu____25775 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25775 = FStar_Syntax_Util.Equal in
                    let uu____25776 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25776
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25780 = equal t1 t2 in
                         (if uu____25780
                          then
                            let uu____25783 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25783
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25788 =
                            let uu____25795 = equal t1 t2 in
                            if uu____25795
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25808 = mk_eq2 wl env orig t1 t2 in
                               match uu____25808 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25788 with
                          | (guard, wl1) ->
                              let uu____25829 = solve_prob orig guard [] wl1 in
                              solve env uu____25829))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25832, FStar_Syntax_Syntax.Tm_match uu____25833) ->
                  let head1 =
                    let uu____25857 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25857
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25897 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25897
                      FStar_Pervasives_Native.fst in
                  ((let uu____25937 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25937
                    then
                      let uu____25941 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25943 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25945 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25941 uu____25943 uu____25945
                    else ());
                   (let no_free_uvars t =
                      (let uu____25959 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25959) &&
                        (let uu____25963 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25963) in
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
                      let uu____25982 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25982 = FStar_Syntax_Util.Equal in
                    let uu____25983 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25983
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25987 = equal t1 t2 in
                         (if uu____25987
                          then
                            let uu____25990 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25990
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25995 =
                            let uu____26002 = equal t1 t2 in
                            if uu____26002
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26015 = mk_eq2 wl env orig t1 t2 in
                               match uu____26015 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25995 with
                          | (guard, wl1) ->
                              let uu____26036 = solve_prob orig guard [] wl1 in
                              solve env uu____26036))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26039, FStar_Syntax_Syntax.Tm_uinst uu____26040) ->
                  let head1 =
                    let uu____26048 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26048
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26088 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26088
                      FStar_Pervasives_Native.fst in
                  ((let uu____26128 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26128
                    then
                      let uu____26132 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26134 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26136 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26132 uu____26134 uu____26136
                    else ());
                   (let no_free_uvars t =
                      (let uu____26150 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26150) &&
                        (let uu____26154 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26154) in
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
                      let uu____26173 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26173 = FStar_Syntax_Util.Equal in
                    let uu____26174 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26174
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26178 = equal t1 t2 in
                         (if uu____26178
                          then
                            let uu____26181 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26181
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26186 =
                            let uu____26193 = equal t1 t2 in
                            if uu____26193
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26206 = mk_eq2 wl env orig t1 t2 in
                               match uu____26206 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26186 with
                          | (guard, wl1) ->
                              let uu____26227 = solve_prob orig guard [] wl1 in
                              solve env uu____26227))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26230, FStar_Syntax_Syntax.Tm_name uu____26231) ->
                  let head1 =
                    let uu____26233 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26233
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26273 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26273
                      FStar_Pervasives_Native.fst in
                  ((let uu____26313 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26313
                    then
                      let uu____26317 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26319 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26321 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26317 uu____26319 uu____26321
                    else ());
                   (let no_free_uvars t =
                      (let uu____26335 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26335) &&
                        (let uu____26339 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26339) in
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
                      let uu____26358 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26358 = FStar_Syntax_Util.Equal in
                    let uu____26359 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26359
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26363 = equal t1 t2 in
                         (if uu____26363
                          then
                            let uu____26366 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26366
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26371 =
                            let uu____26378 = equal t1 t2 in
                            if uu____26378
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26391 = mk_eq2 wl env orig t1 t2 in
                               match uu____26391 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26371 with
                          | (guard, wl1) ->
                              let uu____26412 = solve_prob orig guard [] wl1 in
                              solve env uu____26412))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26415, FStar_Syntax_Syntax.Tm_constant uu____26416) ->
                  let head1 =
                    let uu____26418 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26418
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26458 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26458
                      FStar_Pervasives_Native.fst in
                  ((let uu____26498 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26498
                    then
                      let uu____26502 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26504 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26506 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26502 uu____26504 uu____26506
                    else ());
                   (let no_free_uvars t =
                      (let uu____26520 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26520) &&
                        (let uu____26524 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26524) in
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
                      let uu____26543 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26543 = FStar_Syntax_Util.Equal in
                    let uu____26544 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26544
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26548 = equal t1 t2 in
                         (if uu____26548
                          then
                            let uu____26551 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26551
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26556 =
                            let uu____26563 = equal t1 t2 in
                            if uu____26563
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26576 = mk_eq2 wl env orig t1 t2 in
                               match uu____26576 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26556 with
                          | (guard, wl1) ->
                              let uu____26597 = solve_prob orig guard [] wl1 in
                              solve env uu____26597))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26600, FStar_Syntax_Syntax.Tm_fvar uu____26601) ->
                  let head1 =
                    let uu____26603 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26603
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26649 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26649
                      FStar_Pervasives_Native.fst in
                  ((let uu____26695 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26695
                    then
                      let uu____26699 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26701 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26703 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26699 uu____26701 uu____26703
                    else ());
                   (let no_free_uvars t =
                      (let uu____26717 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26717) &&
                        (let uu____26721 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26721) in
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
                      let uu____26740 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26740 = FStar_Syntax_Util.Equal in
                    let uu____26741 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26741
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26745 = equal t1 t2 in
                         (if uu____26745
                          then
                            let uu____26748 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26748
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26753 =
                            let uu____26760 = equal t1 t2 in
                            if uu____26760
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26773 = mk_eq2 wl env orig t1 t2 in
                               match uu____26773 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26753 with
                          | (guard, wl1) ->
                              let uu____26794 = solve_prob orig guard [] wl1 in
                              solve env uu____26794))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26797, FStar_Syntax_Syntax.Tm_app uu____26798) ->
                  let head1 =
                    let uu____26816 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26816
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26856 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26856
                      FStar_Pervasives_Native.fst in
                  ((let uu____26896 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26896
                    then
                      let uu____26900 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26902 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26904 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26900 uu____26902 uu____26904
                    else ());
                   (let no_free_uvars t =
                      (let uu____26918 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26918) &&
                        (let uu____26922 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26922) in
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
                      let uu____26941 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26941 = FStar_Syntax_Util.Equal in
                    let uu____26942 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26942
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26946 = equal t1 t2 in
                         (if uu____26946
                          then
                            let uu____26949 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26949
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26954 =
                            let uu____26961 = equal t1 t2 in
                            if uu____26961
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26974 = mk_eq2 wl env orig t1 t2 in
                               match uu____26974 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26954 with
                          | (guard, wl1) ->
                              let uu____26995 = solve_prob orig guard [] wl1 in
                              solve env uu____26995))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu____26998,
                 FStar_Syntax_Syntax.Tm_let uu____26999) ->
                  let uu____27026 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu____27026
                  then
                    let uu____27029 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu____27029
                  else
                    (let uu____27032 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu____27032 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____27035, uu____27036) ->
                  let uu____27050 =
                    let uu____27056 =
                      let uu____27058 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____27060 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____27062 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____27064 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27058 uu____27060 uu____27062 uu____27064 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27056) in
                  FStar_Errors.raise_error uu____27050
                    t1.FStar_Syntax_Syntax.pos
              | (uu____27068, FStar_Syntax_Syntax.Tm_let uu____27069) ->
                  let uu____27083 =
                    let uu____27089 =
                      let uu____27091 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____27093 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____27095 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____27097 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27091 uu____27093 uu____27095 uu____27097 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27089) in
                  FStar_Errors.raise_error uu____27083
                    t1.FStar_Syntax_Syntax.pos
              | uu____27101 ->
                  let uu____27106 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu____27106 orig))))
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
          (let uu____27172 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____27172
           then
             let uu____27177 =
               let uu____27179 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu____27179 in
             let uu____27180 =
               let uu____27182 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu____27182 in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27177 uu____27180
           else ());
          (let uu____27186 =
             let uu____27188 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu____27188 in
           if uu____27186
           then
             let uu____27191 =
               mklstr
                 (fun uu____27198 ->
                    let uu____27199 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu____27201 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27199 uu____27201) in
             giveup env uu____27191 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27223 =
                  mklstr
                    (fun uu____27230 ->
                       let uu____27231 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu____27233 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27231 uu____27233) in
                giveup env uu____27223 orig)
             else
               (let uu____27238 =
                  FStar_List.fold_left2
                    (fun uu____27259 ->
                       fun u1 ->
                         fun u2 ->
                           match uu____27259 with
                           | (univ_sub_probs, wl1) ->
                               let uu____27280 =
                                 let uu____27285 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange in
                                 let uu____27286 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange in
                                 sub_prob wl1 uu____27285
                                   FStar_TypeChecker_Common.EQ uu____27286
                                   "effect universes" in
                               (match uu____27280 with
                                | (p, wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu____27238 with
                | (univ_sub_probs, wl1) ->
                    let uu____27306 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu____27306 with
                     | (ret_sub_prob, wl2) ->
                         let uu____27314 =
                           FStar_List.fold_right2
                             (fun uu____27351 ->
                                fun uu____27352 ->
                                  fun uu____27353 ->
                                    match (uu____27351, uu____27352,
                                            uu____27353)
                                    with
                                    | ((a1, uu____27397), (a2, uu____27399),
                                       (arg_sub_probs, wl3)) ->
                                        let uu____27432 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu____27432 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu____27314 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu____27459 =
                                  let uu____27462 =
                                    let uu____27465 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd) in
                                    FStar_List.append arg_sub_probs
                                      uu____27465 in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27462 in
                                FStar_List.append univ_sub_probs uu____27459 in
                              let guard =
                                let guard =
                                  let uu____27487 =
                                    FStar_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu____27487 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f in
                              let wl4 =
                                let uu___3617_27496 = wl3 in
                                {
                                  attempting = (uu___3617_27496.attempting);
                                  wl_deferred = (uu___3617_27496.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3617_27496.wl_deferred_to_tac);
                                  ctr = (uu___3617_27496.ctr);
                                  defer_ok = (uu___3617_27496.defer_ok);
                                  smt_ok = (uu___3617_27496.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3617_27496.umax_heuristic_ok);
                                  tcenv = (uu___3617_27496.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3617_27496.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu____27498 = attempt sub_probs wl5 in
                              solve env uu____27498)))) in
        let solve_layered_sub c11 c21 =
          (let uu____27511 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu____27511
           then
             let uu____27516 =
               let uu____27518 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____27518
                 FStar_Syntax_Print.comp_to_string in
             let uu____27520 =
               let uu____27522 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____27522
                 FStar_Syntax_Print.comp_to_string in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27516 uu____27520
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let subcomp_name =
               let uu____27533 =
                 let uu____27535 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____27535 FStar_Ident.string_of_id in
               let uu____27537 =
                 let uu____27539 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____27539 FStar_Ident.string_of_id in
               FStar_Util.format2 "%s <: %s" uu____27533 uu____27537 in
             let lift_c1 edge =
               let uu____27556 =
                 let uu____27561 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                 FStar_All.pipe_right uu____27561
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env) in
               FStar_All.pipe_right uu____27556
                 (fun uu____27578 ->
                    match uu____27578 with
                    | (c, g) ->
                        let uu____27589 =
                          FStar_Syntax_Util.comp_to_comp_typ c in
                        (uu____27589, g)) in
             let uu____27590 =
               let uu____27602 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name in
               match uu____27602 with
               | FStar_Pervasives_Native.None ->
                   let uu____27616 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name in
                   (match uu____27616 with
                    | FStar_Pervasives_Native.None ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____27635 = lift_c1 edge in
                        (match uu____27635 with
                         | (c12, g_lift) ->
                             let uu____27653 =
                               let uu____27656 =
                                 let uu____27657 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env) in
                                 FStar_All.pipe_right uu____27657
                                   FStar_Syntax_Util.get_stronger_vc_combinator in
                               FStar_All.pipe_right uu____27656
                                 (fun ts ->
                                    let uu____27663 =
                                      let uu____27664 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs in
                                      FStar_All.pipe_right uu____27664
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____27663
                                      (fun uu____27675 ->
                                         FStar_Pervasives_Native.Some
                                           uu____27675)) in
                             (c12, g_lift, uu____27653, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____27681 =
                     let uu____27684 =
                       let uu____27685 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs in
                       FStar_All.pipe_right uu____27685
                         FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____27684
                       (fun uu____27696 ->
                          FStar_Pervasives_Native.Some uu____27696) in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____27681,
                     true) in
             match uu____27590 with
             | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____27712 =
                     mklstr
                       (fun uu____27719 ->
                          let uu____27720 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name in
                          let uu____27722 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____27720 uu____27722) in
                   giveup env uu____27712 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must in
                    let wl1 =
                      let uu___3652_27731 = wl in
                      {
                        attempting = (uu___3652_27731.attempting);
                        wl_deferred = (uu___3652_27731.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3652_27731.wl_deferred_to_tac);
                        ctr = (uu___3652_27731.ctr);
                        defer_ok = (uu___3652_27731.defer_ok);
                        smt_ok = (uu___3652_27731.smt_ok);
                        umax_heuristic_ok =
                          (uu___3652_27731.umax_heuristic_ok);
                        tcenv = (uu___3652_27731.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3652_27731.repr_subcomp_allowed)
                      } in
                    let uu____27732 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____27757 =
                             let uu____27758 = FStar_Syntax_Subst.compress t in
                             uu____27758.FStar_Syntax_Syntax.n in
                           match uu____27757 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____27762 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1, uu____27777)
                               -> is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1, uu____27783) ->
                               is_uvar t1
                           | uu____27808 -> false in
                         FStar_List.fold_right2
                           (fun uu____27842 ->
                              fun uu____27843 ->
                                fun uu____27844 ->
                                  match (uu____27842, uu____27843,
                                          uu____27844)
                                  with
                                  | ((a1, uu____27888), (a2, uu____27890),
                                     (is_sub_probs, wl2)) ->
                                      let uu____27923 = is_uvar a1 in
                                      if uu____27923
                                      then
                                        ((let uu____27933 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns") in
                                          if uu____27933
                                          then
                                            let uu____27938 =
                                              FStar_Syntax_Print.term_to_string
                                                a1 in
                                            let uu____27940 =
                                              FStar_Syntax_Print.term_to_string
                                                a2 in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____27938 uu____27940
                                          else ());
                                         (let uu____27945 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar" in
                                          match uu____27945 with
                                          | (p, wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                    match uu____27732 with
                    | (is_sub_probs, wl2) ->
                        let uu____27973 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type" in
                        (match uu____27973 with
                         | (ret_sub_prob, wl3) ->
                             let stronger_t_shape_error s =
                               let uu____27990 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name in
                               let uu____27992 =
                                 FStar_Syntax_Print.term_to_string stronger_t in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____27990 s uu____27992 in
                             let uu____27995 =
                               let uu____28024 =
                                 let uu____28025 =
                                   FStar_Syntax_Subst.compress stronger_t in
                                 uu____28025.FStar_Syntax_Syntax.n in
                               match uu____28024 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____28085 =
                                     FStar_Syntax_Subst.open_comp bs c in
                                   (match uu____28085 with
                                    | (bs', c3) ->
                                        let a = FStar_List.hd bs' in
                                        let bs1 = FStar_List.tail bs' in
                                        let uu____28148 =
                                          let uu____28167 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one)) in
                                          FStar_All.pipe_right uu____28167
                                            (fun uu____28271 ->
                                               match uu____28271 with
                                               | (l1, l2) ->
                                                   let uu____28344 =
                                                     FStar_List.hd l2 in
                                                   (l1, uu____28344)) in
                                        (match uu____28148 with
                                         | (rest_bs, f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____28449 ->
                                   let uu____28450 =
                                     let uu____28456 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders" in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____28456) in
                                   FStar_Errors.raise_error uu____28450 r in
                             (match uu____27995 with
                              | (a_b, rest_bs, f_b, stronger_c) ->
                                  let uu____28532 =
                                    let uu____28539 =
                                      let uu____28540 =
                                        let uu____28541 =
                                          let uu____28548 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst in
                                          (uu____28548,
                                            (c21.FStar_Syntax_Syntax.result_typ)) in
                                        FStar_Syntax_Syntax.NT uu____28541 in
                                      [uu____28540] in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____28539
                                      (fun b ->
                                         let uu____28564 =
                                           FStar_Syntax_Print.binder_to_string
                                             b in
                                         let uu____28566 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name in
                                         let uu____28568 =
                                           FStar_Range.string_of_range r in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____28564 uu____28566
                                           uu____28568) r in
                                  (match uu____28532 with
                                   | (rest_bs_uvars, g_uvars) ->
                                       let wl4 =
                                         let uu___3717_28578 = wl3 in
                                         {
                                           attempting =
                                             (uu___3717_28578.attempting);
                                           wl_deferred =
                                             (uu___3717_28578.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3717_28578.wl_deferred_to_tac);
                                           ctr = (uu___3717_28578.ctr);
                                           defer_ok =
                                             (uu___3717_28578.defer_ok);
                                           smt_ok = (uu___3717_28578.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3717_28578.umax_heuristic_ok);
                                           tcenv = (uu___3717_28578.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3717_28578.repr_subcomp_allowed)
                                         } in
                                       let substs =
                                         FStar_List.map2
                                           (fun b ->
                                              fun t ->
                                                let uu____28603 =
                                                  let uu____28610 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst in
                                                  (uu____28610, t) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____28603) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars) in
                                       let uu____28627 =
                                         let f_sort_is =
                                           let uu____28637 =
                                             let uu____28640 =
                                               let uu____28641 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____28641.FStar_Syntax_Syntax.sort in
                                             let uu____28650 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name in
                                             let uu____28652 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type" in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____28640 uu____28650 r
                                               uu____28652 in
                                           FStar_All.pipe_right uu____28637
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs)) in
                                         let uu____28659 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_List.fold_left2
                                           (fun uu____28695 ->
                                              fun f_sort_i ->
                                                fun c1_i ->
                                                  match uu____28695 with
                                                  | (ps, wl5) ->
                                                      ((let uu____28717 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns") in
                                                        if uu____28717
                                                        then
                                                          let uu____28722 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i in
                                                          let uu____28724 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____28722
                                                            uu____28724
                                                        else ());
                                                       (let uu____28729 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1" in
                                                        match uu____28729
                                                        with
                                                        | (p, wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____28659 in
                                       (match uu____28627 with
                                        | (f_sub_probs, wl5) ->
                                            let stronger_ct =
                                              let uu____28754 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs) in
                                              FStar_All.pipe_right
                                                uu____28754
                                                FStar_Syntax_Util.comp_to_comp_typ in
                                            let uu____28755 =
                                              let g_sort_is =
                                                let uu____28765 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name in
                                                let uu____28767 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr" in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____28765 r uu____28767 in
                                              let uu____28770 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst) in
                                              FStar_List.fold_left2
                                                (fun uu____28806 ->
                                                   fun g_sort_i ->
                                                     fun c2_i ->
                                                       match uu____28806 with
                                                       | (ps, wl6) ->
                                                           ((let uu____28828
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                             if uu____28828
                                                             then
                                                               let uu____28833
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i in
                                                               let uu____28835
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____28833
                                                                 uu____28835
                                                             else ());
                                                            (let uu____28840
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2" in
                                                             match uu____28840
                                                             with
                                                             | (p, wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____28770 in
                                            (match uu____28755 with
                                             | (g_sub_probs, wl6) ->
                                                 let fml =
                                                   let uu____28867 =
                                                     let uu____28872 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                     let uu____28873 =
                                                       let uu____28874 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                       FStar_Pervasives_Native.fst
                                                         uu____28874 in
                                                     (uu____28872,
                                                       uu____28873) in
                                                   match uu____28867 with
                                                   | (u, wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange in
                                                 let sub_probs =
                                                   let uu____28902 =
                                                     let uu____28905 =
                                                       let uu____28908 =
                                                         let uu____28911 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____28911 in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____28908 in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____28905 in
                                                   ret_sub_prob ::
                                                     uu____28902 in
                                                 let guard =
                                                   let guard =
                                                     let uu____28935 =
                                                       FStar_List.map p_guard
                                                         sub_probs in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____28935 in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                       -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f in
                                                 let wl7 =
                                                   let uu____28946 =
                                                     let uu____28949 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml in
                                                     FStar_All.pipe_left
                                                       (fun uu____28952 ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____28952)
                                                       uu____28949 in
                                                   solve_prob orig
                                                     uu____28946 [] wl6 in
                                                 let uu____28953 =
                                                   attempt sub_probs wl7 in
                                                 solve env uu____28953))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu____28981 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____28983 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu____28983]
               | x -> x in
             let c12 =
               let uu___3775_28986 = c11 in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3775_28986.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3775_28986.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3775_28986.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3775_28986.FStar_Syntax_Syntax.flags)
               } in
             let uu____28987 =
               let uu____28992 =
                 FStar_All.pipe_right
                   (let uu___3778_28994 = c12 in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3778_28994.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3778_28994.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3778_28994.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3778_28994.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____28992
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env) in
             FStar_All.pipe_right uu____28987
               (fun uu____29008 ->
                  match uu____29008 with
                  | (c, g) ->
                      let uu____29015 =
                        let uu____29017 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu____29017 in
                      if uu____29015
                      then
                        let uu____29020 =
                          let uu____29026 =
                            let uu____29028 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu____29030 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____29028 uu____29030 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____29026) in
                        FStar_Errors.raise_error uu____29020 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu____29036 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____29039 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name in
                 Prims.op_Negation uu____29039))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name) in
           if uu____29036
           then
             let uu____29042 =
               mklstr
                 (fun uu____29049 ->
                    let uu____29050 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____29052 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____29050 uu____29052) in
             giveup env uu____29042 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_29063 ->
                        match uu___29_29063 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu____29068 -> false)) in
              let uu____29070 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu____29100)::uu____29101,
                   (wp2, uu____29103)::uu____29104) -> (wp1, wp2)
                | uu____29177 ->
                    let uu____29202 =
                      let uu____29208 =
                        let uu____29210 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu____29212 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____29210 uu____29212 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____29208) in
                    FStar_Errors.raise_error uu____29202
                      env.FStar_TypeChecker_Env.range in
              match uu____29070 with
              | (wpc1, wpc2) ->
                  let uu____29222 = FStar_Util.physical_equality wpc1 wpc2 in
                  if uu____29222
                  then
                    let uu____29225 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu____29225 wl
                  else
                    (let uu____29229 =
                       let uu____29236 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.must uu____29236 in
                     match uu____29229 with
                     | (c2_decl, qualifiers) ->
                         let uu____29257 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu____29257
                         then
                           let c1_repr =
                             let uu____29264 =
                               let uu____29265 =
                                 let uu____29266 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu____29266 in
                               let uu____29267 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____29265 uu____29267 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____29264 in
                           let c2_repr =
                             let uu____29270 =
                               let uu____29271 =
                                 FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu____29272 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____29271 uu____29272 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____29270 in
                           let uu____29274 =
                             let uu____29279 =
                               let uu____29281 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu____29283 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____29281 uu____29283 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____29279 in
                           (match uu____29274 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu____29289 = attempt [prob] wl2 in
                                solve env uu____29289)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____29309 = lift_c1 () in
                                   FStar_All.pipe_right uu____29309
                                     (fun ct ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu____29332 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____29332
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu____29342 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu____29342 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu____29349 =
                                       let uu____29350 =
                                         let uu____29367 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu____29370 =
                                           let uu____29381 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu____29381; wpc1_2] in
                                         (uu____29367, uu____29370) in
                                       FStar_Syntax_Syntax.Tm_app uu____29350 in
                                     FStar_Syntax_Syntax.mk uu____29349 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu____29430 =
                                      let uu____29431 =
                                        let uu____29448 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu____29451 =
                                          let uu____29462 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____29471 =
                                            let uu____29482 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu____29482; wpc1_2] in
                                          uu____29462 :: uu____29471 in
                                        (uu____29448, uu____29451) in
                                      FStar_Syntax_Syntax.Tm_app uu____29431 in
                                    FStar_Syntax_Syntax.mk uu____29430 r)) in
                            (let uu____29536 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____29536
                             then
                               let uu____29541 =
                                 let uu____29543 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string
                                   uu____29543 in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____29541
                             else ());
                            (let uu____29547 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu____29547 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu____29556 =
                                     let uu____29559 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_All.pipe_left
                                       (fun uu____29562 ->
                                          FStar_Pervasives_Native.Some
                                            uu____29562) uu____29559 in
                                   solve_prob orig uu____29556 [] wl1 in
                                 let uu____29563 = attempt [base_prob] wl2 in
                                 solve env uu____29563))))) in
        let uu____29564 = FStar_Util.physical_equality c1 c2 in
        if uu____29564
        then
          let uu____29567 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____29567
        else
          ((let uu____29571 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____29571
            then
              let uu____29576 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____29578 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29576
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29578
            else ());
           (let uu____29583 =
              let uu____29592 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____29595 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____29592, uu____29595) in
            match uu____29583 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____29613),
                    FStar_Syntax_Syntax.Total (t2, uu____29615)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29632 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29632 wl
                 | (FStar_Syntax_Syntax.GTotal uu____29634,
                    FStar_Syntax_Syntax.Total uu____29635) ->
                     let uu____29652 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu____29652 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____29656),
                    FStar_Syntax_Syntax.Total (t2, uu____29658)) ->
                     let uu____29675 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29675 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____29678),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29680)) ->
                     let uu____29697 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29697 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____29700),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29702)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29719 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29719 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____29722),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29724)) ->
                     let uu____29741 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu____29741 orig
                 | (FStar_Syntax_Syntax.GTotal uu____29744,
                    FStar_Syntax_Syntax.Comp uu____29745) ->
                     let uu____29754 =
                       let uu___3902_29757 = problem in
                       let uu____29760 =
                         let uu____29761 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29761 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3902_29757.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29760;
                         FStar_TypeChecker_Common.relation =
                           (uu___3902_29757.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3902_29757.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3902_29757.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3902_29757.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3902_29757.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3902_29757.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3902_29757.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3902_29757.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29754 wl
                 | (FStar_Syntax_Syntax.Total uu____29762,
                    FStar_Syntax_Syntax.Comp uu____29763) ->
                     let uu____29772 =
                       let uu___3902_29775 = problem in
                       let uu____29778 =
                         let uu____29779 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29779 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3902_29775.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29778;
                         FStar_TypeChecker_Common.relation =
                           (uu___3902_29775.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3902_29775.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3902_29775.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3902_29775.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3902_29775.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3902_29775.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3902_29775.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3902_29775.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29772 wl
                 | (FStar_Syntax_Syntax.Comp uu____29780,
                    FStar_Syntax_Syntax.GTotal uu____29781) ->
                     let uu____29790 =
                       let uu___3914_29793 = problem in
                       let uu____29796 =
                         let uu____29797 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29797 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3914_29793.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3914_29793.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3914_29793.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29796;
                         FStar_TypeChecker_Common.element =
                           (uu___3914_29793.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3914_29793.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3914_29793.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3914_29793.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3914_29793.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3914_29793.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29790 wl
                 | (FStar_Syntax_Syntax.Comp uu____29798,
                    FStar_Syntax_Syntax.Total uu____29799) ->
                     let uu____29808 =
                       let uu___3914_29811 = problem in
                       let uu____29814 =
                         let uu____29815 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29815 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3914_29811.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3914_29811.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3914_29811.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29814;
                         FStar_TypeChecker_Common.element =
                           (uu___3914_29811.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3914_29811.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3914_29811.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3914_29811.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3914_29811.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3914_29811.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29808 wl
                 | (FStar_Syntax_Syntax.Comp uu____29816,
                    FStar_Syntax_Syntax.Comp uu____29817) ->
                     let uu____29818 =
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
                     if uu____29818
                     then
                       let uu____29821 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____29821 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29828 =
                            let uu____29833 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu____29833
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29842 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____29843 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____29842, uu____29843)) in
                          match uu____29828 with
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
                           (let uu____29851 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____29851
                            then
                              let uu____29856 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu____29858 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29856 uu____29858
                            else ());
                           (let uu____29863 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu____29863
                            then solve_layered_sub c12 c22
                            else
                              (let uu____29868 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu____29868 with
                               | FStar_Pervasives_Native.None ->
                                   let uu____29871 =
                                     mklstr
                                       (fun uu____29878 ->
                                          let uu____29879 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu____29881 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____29879 uu____29881) in
                                   giveup env uu____29871 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu____29892 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_All.pipe_right uu____29892 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____29942 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____29942 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____29967 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29998 ->
                match uu____29998 with
                | (u1, u2) ->
                    let uu____30006 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____30008 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____30006 uu____30008)) in
      FStar_All.pipe_right uu____29967 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial, [], (uu____30045, [])) when
          let uu____30072 = FStar_Options.print_implicits () in
          Prims.op_Negation uu____30072 -> "{}"
      | uu____30075 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____30102 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu____30102
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu____30133 =
              FStar_List.map
                (fun uu____30147 ->
                   match uu____30147 with
                   | (msg, x) ->
                       let uu____30158 =
                         let uu____30160 = prob_to_string env x in
                         Prims.op_Hat ": " uu____30160 in
                       Prims.op_Hat msg uu____30158) defs in
            FStar_All.pipe_right uu____30133 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____30170 = carry g.FStar_TypeChecker_Common.deferred in
          let uu____30172 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu____30174 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30170 uu____30172 uu____30174 imps
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
                  let uu____30231 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu____30231
                  then
                    let uu____30239 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu____30241 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30239
                      (rel_to_string rel) uu____30241
                  else "TOP" in
                let uu____30247 =
                  new_problem wl env lhs rel rhs elt loc reason in
                match uu____30247 with
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
              let uu____30307 =
                let uu____30310 = FStar_TypeChecker_Env.get_range env in
                FStar_All.pipe_left
                  (fun uu____30313 ->
                     FStar_Pervasives_Native.Some uu____30313) uu____30310 in
              FStar_Syntax_Syntax.new_bv uu____30307 t1 in
            let uu____30314 =
              let uu____30319 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30319 in
            match uu____30314 with | (p, wl1) -> (p, x, wl1)
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
        (let uu____30391 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu____30391
         then
           let uu____30396 =
             FStar_Common.string_of_list
               (fun p -> FStar_Util.string_of_int (p_pid p)) probs.attempting in
           FStar_Util.print1 "solving problems %s {\n" uu____30396
         else ());
        (let uu____30403 =
           FStar_Util.record_time (fun uu____30410 -> solve env probs) in
         match uu____30403 with
         | (sol, ms) ->
             ((let uu____30424 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu____30424
               then
                 let uu____30429 = FStar_Util.string_of_int ms in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30429
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu____30445 =
                     FStar_Util.record_time
                       (fun uu____30452 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu____30445 with
                    | ((), ms1) ->
                        ((let uu____30465 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu____30465
                          then
                            let uu____30470 = FStar_Util.string_of_int ms1 in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30470
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu____30484 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu____30484
                     then
                       let uu____30491 = explain env d s in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30491
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
          ((let uu____30519 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____30519
            then
              let uu____30524 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30524
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu____30532 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____30532
             then
               let uu____30537 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30537
             else ());
            (let f2 =
               let uu____30543 =
                 let uu____30544 = FStar_Syntax_Util.unmeta f1 in
                 uu____30544.FStar_Syntax_Syntax.n in
               match uu____30543 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30548 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___4034_30549 = g in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4034_30549.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4034_30549.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4034_30549.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4034_30549.FStar_TypeChecker_Common.implicits)
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
            let uu____30601 =
              let uu____30602 =
                let uu____30603 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30604 ->
                       FStar_TypeChecker_Common.NonTrivial uu____30604) in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30603;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu____30602 in
            FStar_All.pipe_left
              (fun uu____30611 -> FStar_Pervasives_Native.Some uu____30611)
              uu____30601
let with_guard_no_simp :
  'uuuuuu30621 .
    'uuuuuu30621 ->
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
            let uu____30670 =
              let uu____30671 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30672 ->
                     FStar_TypeChecker_Common.NonTrivial uu____30672) in
              {
                FStar_TypeChecker_Common.guard_f = uu____30671;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              } in
            FStar_Pervasives_Native.Some uu____30670
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
          (let uu____30705 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____30705
           then
             let uu____30710 = FStar_Syntax_Print.term_to_string t1 in
             let uu____30712 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30710
               uu____30712
           else ());
          (let uu____30717 =
             let uu____30722 = FStar_TypeChecker_Env.get_range env in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30722 in
           match uu____30717 with
           | (prob, wl) ->
               let g =
                 let uu____30730 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30740 -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____30730 in
               ((let uu____30762 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____30762
                 then
                   let uu____30767 =
                     FStar_Common.string_of_option (guard_to_string env) g in
                   FStar_Util.print1 "} res = %s\n" uu____30767
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
        let uu____30788 = try_teq true env t1 t2 in
        match uu____30788 with
        | FStar_Pervasives_Native.None ->
            ((let uu____30793 = FStar_TypeChecker_Env.get_range env in
              let uu____30794 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____30793 uu____30794);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30802 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____30802
              then
                let uu____30807 = FStar_Syntax_Print.term_to_string t1 in
                let uu____30809 = FStar_Syntax_Print.term_to_string t2 in
                let uu____30811 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30807
                  uu____30809 uu____30811
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
        (let uu____30835 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____30835
         then
           let uu____30840 = FStar_Syntax_Print.term_to_string t1 in
           let uu____30842 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30840
             uu____30842
         else ());
        (let uu____30847 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu____30847 with
         | (prob, x, wl) ->
             let g =
               let uu____30862 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30873 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____30862 in
             ((let uu____30895 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____30895
               then
                 let uu____30900 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30900
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30908 =
                     let uu____30909 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu____30909 g1 in
                   FStar_Pervasives_Native.Some uu____30908)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____30931 = FStar_TypeChecker_Env.get_range env in
          let uu____30932 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____30931 uu____30932
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
        (let uu____30961 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____30961
         then
           let uu____30966 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____30968 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30966 uu____30968
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30979 =
           let uu____30986 = FStar_TypeChecker_Env.get_range env in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30986 "sub_comp" in
         match uu____30979 with
         | (prob, wl) ->
             let wl1 =
               let uu___4107_30997 = wl in
               {
                 attempting = (uu___4107_30997.attempting);
                 wl_deferred = (uu___4107_30997.wl_deferred);
                 wl_deferred_to_tac = (uu___4107_30997.wl_deferred_to_tac);
                 ctr = (uu___4107_30997.ctr);
                 defer_ok = (uu___4107_30997.defer_ok);
                 smt_ok = (uu___4107_30997.smt_ok);
                 umax_heuristic_ok = (uu___4107_30997.umax_heuristic_ok);
                 tcenv = (uu___4107_30997.tcenv);
                 wl_implicits = (uu___4107_30997.wl_implicits);
                 repr_subcomp_allowed = true
               } in
             let prob1 = FStar_TypeChecker_Common.CProb prob in
             (def_check_prob "sub_comp" prob1;
              (let uu____31002 =
                 FStar_Util.record_time
                   (fun uu____31014 ->
                      let uu____31015 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____31026 -> FStar_Pervasives_Native.None) in
                      FStar_All.pipe_left (with_guard env prob1) uu____31015) in
               match uu____31002 with
               | (r, ms) ->
                   ((let uu____31058 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench") in
                     if uu____31058
                     then
                       let uu____31063 = FStar_Syntax_Print.comp_to_string c1 in
                       let uu____31065 = FStar_Syntax_Print.comp_to_string c2 in
                       let uu____31067 = FStar_Util.string_of_int ms in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____31063 uu____31065
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____31067
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
      fun uu____31105 ->
        match uu____31105 with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31148 =
                 let uu____31154 =
                   let uu____31156 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____31158 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31156 uu____31158 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31154) in
               let uu____31162 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____31148 uu____31162) in
            let equiv v v' =
              let uu____31175 =
                let uu____31180 = FStar_Syntax_Subst.compress_univ v in
                let uu____31181 = FStar_Syntax_Subst.compress_univ v' in
                (uu____31180, uu____31181) in
              match uu____31175 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31205 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v ->
                      let uu____31236 = FStar_Syntax_Subst.compress_univ v in
                      match uu____31236 with
                      | FStar_Syntax_Syntax.U_unif uu____31243 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31274 ->
                                    match uu____31274 with
                                    | (u, v') ->
                                        let uu____31283 = equiv v v' in
                                        if uu____31283
                                        then
                                          let uu____31288 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____31288 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____31309 -> [])) in
            let uu____31314 =
              let wl =
                let uu___4150_31318 = empty_worklist env in
                {
                  attempting = (uu___4150_31318.attempting);
                  wl_deferred = (uu___4150_31318.wl_deferred);
                  wl_deferred_to_tac = (uu___4150_31318.wl_deferred_to_tac);
                  ctr = (uu___4150_31318.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4150_31318.smt_ok);
                  umax_heuristic_ok = (uu___4150_31318.umax_heuristic_ok);
                  tcenv = (uu___4150_31318.tcenv);
                  wl_implicits = (uu___4150_31318.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4150_31318.repr_subcomp_allowed)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31337 ->
                      match uu____31337 with
                      | (lb, v) ->
                          let uu____31344 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu____31344 with
                           | USolved wl1 -> ()
                           | uu____31347 -> fail lb v))) in
            let rec check_ineq uu____31358 =
              match uu____31358 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu____31370) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____31398,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____31400,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____31413) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v1)))
                   | (uu____31421, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v2 -> check_ineq (u1, v2)))
                   | uu____31430 -> false) in
            let uu____31436 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31453 ->
                      match uu____31453 with
                      | (u, v) ->
                          let uu____31461 = check_ineq (u, v) in
                          if uu____31461
                          then true
                          else
                            ((let uu____31469 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____31469
                              then
                                let uu____31474 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____31476 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" uu____31474
                                  uu____31476
                              else ());
                             false))) in
            if uu____31436
            then ()
            else
              ((let uu____31486 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____31486
                then
                  ((let uu____31492 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31492);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31504 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31504))
                else ());
               (let uu____31517 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31517))
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
          let fail uu____31599 =
            match uu____31599 with
            | (d, s) ->
                let msg = explain env d s in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d) in
          let wl =
            let uu___4228_31626 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred in
            {
              attempting = (uu___4228_31626.attempting);
              wl_deferred = (uu___4228_31626.wl_deferred);
              wl_deferred_to_tac = (uu___4228_31626.wl_deferred_to_tac);
              ctr = (uu___4228_31626.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4228_31626.umax_heuristic_ok);
              tcenv = (uu___4228_31626.tcenv);
              wl_implicits = (uu___4228_31626.wl_implicits);
              repr_subcomp_allowed = (uu___4228_31626.repr_subcomp_allowed)
            } in
          (let uu____31629 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____31629
           then
             let uu____31634 = FStar_Util.string_of_bool defer_ok in
             let uu____31636 = wl_to_string wl in
             let uu____31638 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits) in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31634 uu____31636 uu____31638
           else ());
          (let g1 =
             let uu____31644 = solve_and_commit env wl fail in
             match uu____31644 with
             | FStar_Pervasives_Native.Some
                 (uu____31653::uu____31654, uu____31655, uu____31656) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred, defer_to_tac, imps) ->
                 let uu___4245_31690 = g in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4245_31690.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4245_31690.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31696 ->
                 failwith "Impossible: should have raised a failure already" in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1 in
            (let uu____31709 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook") in
             if uu____31709
             then
               let uu____31714 = guard_to_string env g2 in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____31714
             else ());
            (let uu___4253_31719 = g2 in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4253_31719.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4253_31719.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4253_31719.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4253_31719.FStar_TypeChecker_Common.implicits)
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
          (let uu____31815 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu____31815
           then
             let uu____31820 = guard_to_string env g in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31820
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g in
           let ret_g =
             let uu___4270_31827 = g1 in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4270_31827.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4270_31827.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4270_31827.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4270_31827.FStar_TypeChecker_Common.implicits)
             } in
           let uu____31828 =
             let uu____31830 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu____31830 in
           if uu____31828
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____31842 = FStar_TypeChecker_Env.get_range env in
                      let uu____31843 =
                        let uu____31845 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31845 in
                      FStar_Errors.diag uu____31842 uu____31843)
                   else ();
                   (let vc1 =
                      let uu____31851 =
                        let uu____31855 =
                          let uu____31857 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu____31857 in
                        FStar_Pervasives_Native.Some uu____31855 in
                      FStar_Profiling.profile
                        (fun uu____31860 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31851 "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu____31864 = FStar_TypeChecker_Env.get_range env in
                       let uu____31865 =
                         let uu____31867 =
                           FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31867 in
                       FStar_Errors.diag uu____31864 uu____31865)
                    else ();
                    (let uu____31873 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31873 "discharge_guard'" env vc1);
                    (let uu____31875 =
                       FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu____31875 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____31884 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____31885 =
                                 let uu____31887 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31887 in
                               FStar_Errors.diag uu____31884 uu____31885)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____31897 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____31898 =
                                 let uu____31900 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31900 in
                               FStar_Errors.diag uu____31897 uu____31898)
                            else ();
                            (let vcs =
                               let uu____31914 = FStar_Options.use_tactics () in
                               if uu____31914
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31936 ->
                                      (let uu____31938 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_All.pipe_left
                                         (fun uu____31940 -> ()) uu____31938);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31983 ->
                                               match uu____31983 with
                                               | (env1, goal, opts) ->
                                                   let uu____31999 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu____31999, opts)))))
                               else
                                 (let uu____32003 =
                                    let uu____32010 = FStar_Options.peek () in
                                    (env, vc2, uu____32010) in
                                  [uu____32003]) in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____32043 ->
                                     match uu____32043 with
                                     | (env1, goal, opts) ->
                                         let uu____32053 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu____32053 with
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
                                                 (let uu____32064 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____32065 =
                                                    let uu____32067 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu____32069 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____32067 uu____32069 in
                                                  FStar_Errors.diag
                                                    uu____32064 uu____32065)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____32076 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____32077 =
                                                    let uu____32079 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____32079 in
                                                  FStar_Errors.diag
                                                    uu____32076 uu____32077)
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
      let uu____32097 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____32097 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____32106 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____32106
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____32120 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____32120 with
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
        let uu____32150 = try_teq false env t1 t2 in
        match uu____32150 with
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
             let uu____32205 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu____32205 with
             | (ctx_u, r) ->
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                 let uu____32215 =
                   let uu____32216 = FStar_Syntax_Subst.compress t_norm in
                   uu____32216.FStar_Syntax_Syntax.n in
                 (match uu____32215 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu____32222 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____32222
                        (fun uu____32225 ->
                           FStar_Pervasives_Native.Some uu____32225)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____32227) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu____32232 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____32232
                        (fun uu____32235 ->
                           FStar_Pervasives_Native.Some uu____32235)
                  | uu____32236 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_List.fold_left
               (fun b ->
                  fun imp ->
                    let uu____32249 =
                      let uu____32251 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_All.pipe_right uu____32251 FStar_Util.is_none in
                    if uu____32249
                    then
                      let uu____32259 = imp_value imp in
                      match uu____32259 with
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
        let uu____32288 =
          if is_tac
          then (false, true)
          else
            (((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
                (Prims.op_Negation env.FStar_TypeChecker_Env.lax)), false) in
        match uu____32288 with
        | (must_total, forcelax) ->
            let rec unresolved ctx_u =
              let uu____32324 =
                FStar_Syntax_Unionfind.find
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
              match uu____32324 with
              | FStar_Pervasives_Native.Some r ->
                  (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                   | FStar_Pervasives_Native.None -> false
                   | FStar_Pervasives_Native.Some uu____32331 ->
                       let uu____32332 =
                         let uu____32333 = FStar_Syntax_Subst.compress r in
                         uu____32333.FStar_Syntax_Syntax.n in
                       (match uu____32332 with
                        | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____32338)
                            -> unresolved ctx_u'
                        | uu____32355 -> false))
              | FStar_Pervasives_Native.None -> true in
            let rec until_fixpoint acc implicits =
              let uu____32379 = acc in
              match uu____32379 with
              | (out, changed) ->
                  (match implicits with
                   | [] ->
                       if Prims.op_Negation changed
                       then
                         let uu____32390 =
                           try_solve_single_valued_implicits env is_tac out in
                         (match uu____32390 with
                          | (out1, changed1) ->
                              if changed1
                              then until_fixpoint ([], false) out1
                              else out1)
                       else until_fixpoint ([], false) out
                   | hd::tl ->
                       let uu____32413 = hd in
                       (match uu____32413 with
                        | { FStar_TypeChecker_Common.imp_reason = reason;
                            FStar_TypeChecker_Common.imp_uvar = ctx_u;
                            FStar_TypeChecker_Common.imp_tm = tm;
                            FStar_TypeChecker_Common.imp_range = r;_} ->
                            if
                              ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                = FStar_Syntax_Syntax.Allow_unresolved
                            then until_fixpoint (out, true) tl
                            else
                              (let uu____32424 = unresolved ctx_u in
                               if uu____32424
                               then
                                 match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                     (env_dyn, tau)) ->
                                     let env1 = FStar_Dyn.undyn env_dyn in
                                     ((let uu____32435 =
                                         FStar_TypeChecker_Env.debug env1
                                           (FStar_Options.Other "Tac") in
                                       if uu____32435
                                       then
                                         let uu____32439 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             ctx_u in
                                         FStar_Util.print1
                                           "Running tactic for meta-arg %s\n"
                                           uu____32439
                                       else ());
                                      (let t =
                                         env1.FStar_TypeChecker_Env.synth_hook
                                           env1
                                           (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                           tau in
                                       let extra =
                                         let uu____32448 =
                                           teq_nosmt env1 t tm in
                                         match uu____32448 with
                                         | FStar_Pervasives_Native.None ->
                                             failwith
                                               "resolve_implicits: unifying with an unresolved uvar failed?"
                                         | FStar_Pervasives_Native.Some g1 ->
                                             g1.FStar_TypeChecker_Common.implicits in
                                       let ctx_u1 =
                                         let uu___4415_32458 = ctx_u in
                                         {
                                           FStar_Syntax_Syntax.ctx_uvar_head
                                             =
                                             (uu___4415_32458.FStar_Syntax_Syntax.ctx_uvar_head);
                                           FStar_Syntax_Syntax.ctx_uvar_gamma
                                             =
                                             (uu___4415_32458.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                           FStar_Syntax_Syntax.ctx_uvar_binders
                                             =
                                             (uu___4415_32458.FStar_Syntax_Syntax.ctx_uvar_binders);
                                           FStar_Syntax_Syntax.ctx_uvar_typ =
                                             (uu___4415_32458.FStar_Syntax_Syntax.ctx_uvar_typ);
                                           FStar_Syntax_Syntax.ctx_uvar_reason
                                             =
                                             (uu___4415_32458.FStar_Syntax_Syntax.ctx_uvar_reason);
                                           FStar_Syntax_Syntax.ctx_uvar_should_check
                                             =
                                             (uu___4415_32458.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                           FStar_Syntax_Syntax.ctx_uvar_range
                                             =
                                             (uu___4415_32458.FStar_Syntax_Syntax.ctx_uvar_range);
                                           FStar_Syntax_Syntax.ctx_uvar_meta
                                             = FStar_Pervasives_Native.None
                                         } in
                                       let hd1 =
                                         let uu___4418_32460 = hd in
                                         {
                                           FStar_TypeChecker_Common.imp_reason
                                             =
                                             (uu___4418_32460.FStar_TypeChecker_Common.imp_reason);
                                           FStar_TypeChecker_Common.imp_uvar
                                             = ctx_u1;
                                           FStar_TypeChecker_Common.imp_tm =
                                             (uu___4418_32460.FStar_TypeChecker_Common.imp_tm);
                                           FStar_TypeChecker_Common.imp_range
                                             =
                                             (uu___4418_32460.FStar_TypeChecker_Common.imp_range)
                                         } in
                                       until_fixpoint (out, true)
                                         (FStar_List.append extra tl)))
                                 | uu____32463 ->
                                     until_fixpoint ((hd :: out), changed) tl
                               else
                                 if
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                     = FStar_Syntax_Syntax.Allow_untyped
                                 then until_fixpoint (out, true) tl
                                 else
                                   (let env1 =
                                      let uu___4423_32475 = env in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4423_32475.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4423_32475.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4423_32475.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4423_32475.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4423_32475.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4423_32475.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4423_32475.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4423_32475.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4423_32475.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4423_32475.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4423_32475.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4423_32475.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4423_32475.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4423_32475.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4423_32475.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4423_32475.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4423_32475.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4423_32475.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4423_32475.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___4423_32475.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4423_32475.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4423_32475.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4423_32475.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4423_32475.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4423_32475.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4423_32475.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4423_32475.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4423_32475.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4423_32475.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4423_32475.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4423_32475.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4423_32475.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4423_32475.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4423_32475.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4423_32475.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4423_32475.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4423_32475.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4423_32475.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4423_32475.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4423_32475.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4423_32475.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4423_32475.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4423_32475.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4423_32475.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4423_32475.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4423_32475.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    let tm1 =
                                      norm_with_steps
                                        "FStar.TypeChecker.Rel.norm_with_steps.8"
                                        [FStar_TypeChecker_Env.Beta] env1 tm in
                                    let env2 =
                                      if forcelax
                                      then
                                        let uu___4428_32480 = env1 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___4428_32480.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___4428_32480.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___4428_32480.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___4428_32480.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___4428_32480.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___4428_32480.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___4428_32480.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___4428_32480.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___4428_32480.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___4428_32480.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___4428_32480.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___4428_32480.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___4428_32480.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___4428_32480.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___4428_32480.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___4428_32480.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___4428_32480.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___4428_32480.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___4428_32480.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___4428_32480.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___4428_32480.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___4428_32480.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___4428_32480.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___4428_32480.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___4428_32480.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___4428_32480.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___4428_32480.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___4428_32480.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___4428_32480.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___4428_32480.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___4428_32480.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (uu___4428_32480.FStar_TypeChecker_Env.enable_defer_to_tac)
                                        }
                                      else env1 in
                                    (let uu____32485 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env2)
                                         (FStar_Options.Other "Rel") in
                                     if uu____32485
                                     then
                                       let uu____32490 =
                                         FStar_Syntax_Print.uvar_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                       let uu____32492 =
                                         FStar_Syntax_Print.term_to_string
                                           tm1 in
                                       let uu____32494 =
                                         FStar_Syntax_Print.term_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                       let uu____32496 =
                                         FStar_Range.string_of_range r in
                                       FStar_Util.print5
                                         "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                         uu____32490 uu____32492 uu____32494
                                         reason uu____32496
                                     else ());
                                    (let g1 =
                                       try
                                         (fun uu___4434_32503 ->
                                            match () with
                                            | () ->
                                                env2.FStar_TypeChecker_Env.check_type_of
                                                  must_total env2 tm1
                                                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                           ()
                                       with
                                       | e when FStar_Errors.handleable e ->
                                           ((let uu____32510 =
                                               let uu____32520 =
                                                 let uu____32528 =
                                                   let uu____32530 =
                                                     FStar_Syntax_Print.uvar_to_string
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu____32532 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2 tm1 in
                                                   let uu____32534 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                   FStar_Util.format3
                                                     "Failed while checking implicit %s set to %s of expected type %s"
                                                     uu____32530 uu____32532
                                                     uu____32534 in
                                                 (FStar_Errors.Error_BadImplicit,
                                                   uu____32528, r) in
                                               [uu____32520] in
                                             FStar_Errors.add_errors
                                               uu____32510);
                                            FStar_Exn.raise e) in
                                     let g' =
                                       let uu____32553 =
                                         discharge_guard'
                                           (FStar_Pervasives_Native.Some
                                              (fun uu____32564 ->
                                                 let uu____32565 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm1 in
                                                 let uu____32567 =
                                                   FStar_Range.string_of_range
                                                     r in
                                                 let uu____32569 =
                                                   FStar_Range.string_of_range
                                                     tm1.FStar_Syntax_Syntax.pos in
                                                 FStar_Util.format4
                                                   "%s (Introduced at %s for %s resolved at %s)"
                                                   uu____32565 uu____32567
                                                   reason uu____32569)) env2
                                           g1 true in
                                       match uu____32553 with
                                       | FStar_Pervasives_Native.Some g2 ->
                                           g2
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                                     until_fixpoint
                                       ((FStar_List.append
                                           g'.FStar_TypeChecker_Common.implicits
                                           out), true) tl))))) in
            let uu___4446_32577 = g in
            let uu____32578 =
              until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4446_32577.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4446_32577.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4446_32577.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4446_32577.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = uu____32578
            }
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu____32593 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____32593
       then
         let uu____32598 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32598
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
      (let uu____32628 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____32628
       then
         let uu____32633 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32633
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____32640 = discharge_guard env g2 in
           FStar_All.pipe_left (fun uu____32641 -> ()) uu____32640
       | imp::uu____32643 ->
           let uu____32646 =
             let uu____32652 =
               let uu____32654 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____32656 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____32654 uu____32656
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32652) in
           FStar_Errors.raise_error uu____32646
             imp.FStar_TypeChecker_Common.imp_range)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32676 = teq env t1 t2 in
        force_trivial_guard env uu____32676
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32695 = teq_nosmt env t1 t2 in
        match uu____32695 with
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
          (let uu____32731 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu____32731
           then
             let uu____32736 =
               let uu____32738 =
                 FStar_All.pipe_right reason FStar_Util.is_none in
               if uu____32738
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must in
             let uu____32755 = FStar_Syntax_Print.term_to_string t1 in
             let uu____32757 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____32736
               uu____32755 uu____32757
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___4484_32773 = FStar_TypeChecker_Common.trivial_guard in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4484_32773.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4484_32773.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4484_32773.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4484_32773.FStar_TypeChecker_Common.implicits)
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
        (let uu____32809 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____32809
         then
           let uu____32814 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____32816 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32814
             uu____32816
         else ());
        (let uu____32821 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____32821 with
         | (prob, x, wl) ->
             let g =
               let uu____32840 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32851 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____32840 in
             ((let uu____32873 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____32873
               then
                 let uu____32878 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____32880 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____32882 =
                   let uu____32884 = FStar_Util.must g in
                   guard_to_string env uu____32884 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32878 uu____32880 uu____32882
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
        let uu____32921 = check_subtyping env t1 t2 in
        match uu____32921 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____32940 =
              let uu____32941 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu____32941 g in
            FStar_Pervasives_Native.Some uu____32940
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32960 = check_subtyping env t1 t2 in
        match uu____32960 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____32979 =
              let uu____32980 =
                let uu____32981 = FStar_Syntax_Syntax.mk_binder x in
                [uu____32981] in
              FStar_TypeChecker_Env.close_guard env uu____32980 g in
            FStar_Pervasives_Native.Some uu____32979
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____33019 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____33019
         then
           let uu____33024 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____33026 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____33024
             uu____33026
         else ());
        (let uu____33031 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____33031 with
         | (prob, x, wl) ->
             let g =
               let uu____33046 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____33057 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____33046 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____33082 =
                      let uu____33083 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____33083] in
                    FStar_TypeChecker_Env.close_guard env uu____33082 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____33124 = subtype_nosmt env t1 t2 in
        match uu____33124 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)