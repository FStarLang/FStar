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
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None in
                                          (match uu____17409 with
                                           | (uu____17425, w, wl1) ->
                                               let w_app =
                                                 let uu____17429 =
                                                   FStar_List.map
                                                     (fun uu____17440 ->
                                                        match uu____17440
                                                        with
                                                        | (z, uu____17448) ->
                                                            let uu____17453 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____17453) zs in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____17429
                                                   w.FStar_Syntax_Syntax.pos in
                                               ((let uu____17455 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____17455
                                                 then
                                                   let uu____17460 =
                                                     let uu____17464 =
                                                       flex_t_to_string lhs in
                                                     let uu____17466 =
                                                       let uu____17470 =
                                                         flex_t_to_string rhs in
                                                       let uu____17472 =
                                                         let uu____17476 =
                                                           term_to_string w in
                                                         let uu____17478 =
                                                           let uu____17482 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs) in
                                                           let uu____17491 =
                                                             let uu____17495
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs) in
                                                             let uu____17504
                                                               =
                                                               let uu____17508
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs in
                                                               [uu____17508] in
                                                             uu____17495 ::
                                                               uu____17504 in
                                                           uu____17482 ::
                                                             uu____17491 in
                                                         uu____17476 ::
                                                           uu____17478 in
                                                       uu____17470 ::
                                                         uu____17472 in
                                                     uu____17464 ::
                                                       uu____17466 in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17460
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17525 =
                                                       let uu____17530 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs)) in
                                                       (u_lhs, uu____17530) in
                                                     TERM uu____17525 in
                                                   let uu____17531 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   if uu____17531
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17539 =
                                                          let uu____17544 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          (u_rhs,
                                                            uu____17544) in
                                                        TERM uu____17539 in
                                                      [s1; s2]) in
                                                 let uu____17545 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1 in
                                                 solve env uu____17545))))))
                     | uu____17546 ->
                         let uu____17563 =
                           FStar_Thunk.mkv "flex-flex: non-patterns" in
                         giveup_or_defer env orig wl uu____17563)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____17617 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu____17617
            then
              let uu____17622 = FStar_Syntax_Print.term_to_string t1 in
              let uu____17624 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____17626 = FStar_Syntax_Print.term_to_string t2 in
              let uu____17628 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17622 uu____17624 uu____17626 uu____17628
            else ());
           (let uu____17639 = FStar_Syntax_Util.head_and_args t1 in
            match uu____17639 with
            | (head1, args1) ->
                let uu____17682 = FStar_Syntax_Util.head_and_args t2 in
                (match uu____17682 with
                 | (head2, args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17752 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu____17752 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17757 =
                                defer_lit "universe constraints" orig wl3 in
                              k false uu____17757) in
                     let nargs = FStar_List.length args1 in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17778 =
                         mklstr
                           (fun uu____17789 ->
                              let uu____17790 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____17792 = args_to_string args1 in
                              let uu____17796 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu____17798 = args_to_string args2 in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17790 uu____17792 uu____17796
                                uu____17798) in
                       giveup env1 uu____17778 orig
                     else
                       (let uu____17805 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17810 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu____17810 = FStar_Syntax_Util.Equal) in
                        if uu____17805
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2606_17814 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2606_17814.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2606_17814.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2606_17814.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2606_17814.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2606_17814.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2606_17814.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2606_17814.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2606_17814.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu____17824 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu____17824
                                    else solve env1 wl2))
                        else
                          (let uu____17829 = base_and_refinement env1 t1 in
                           match uu____17829 with
                           | (base1, refinement1) ->
                               let uu____17854 = base_and_refinement env1 t2 in
                               (match uu____17854 with
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
                                           let uu____18019 =
                                             FStar_List.fold_right
                                               (fun uu____18059 ->
                                                  fun uu____18060 ->
                                                    match (uu____18059,
                                                            uu____18060)
                                                    with
                                                    | (((a1, uu____18112),
                                                        (a2, uu____18114)),
                                                       (probs, wl3)) ->
                                                        let uu____18163 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu____18163
                                                         with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu____18019 with
                                           | (subprobs, wl3) ->
                                               ((let uu____18206 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____18206
                                                 then
                                                   let uu____18211 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18211
                                                 else ());
                                                (let uu____18217 =
                                                   FStar_Options.defensive () in
                                                 if uu____18217
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
                                                    (let uu____18244 =
                                                       mk_sub_probs wl3 in
                                                     match uu____18244 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu____18260 =
                                                             FStar_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18260 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu____18268 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2
                                                           uu____18268)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu____18293 =
                                                    mk_sub_probs wl3 in
                                                  match uu____18293 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu____18309 =
                                                          FStar_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18309 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu____18317 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu____18317) in
                                         let unfold_and_retry d env2 wl2
                                           uu____18345 =
                                           match uu____18345 with
                                           | (prob, reason) ->
                                               ((let uu____18362 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____18362
                                                 then
                                                   let uu____18367 =
                                                     prob_to_string env2 orig in
                                                   let uu____18369 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____18367 uu____18369
                                                 else ());
                                                (let uu____18375 =
                                                   let uu____18384 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu____18387 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu____18384, uu____18387) in
                                                 match uu____18375 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18400 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu____18400 with
                                                      | (head1', uu____18418)
                                                          ->
                                                          let uu____18443 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu____18443
                                                           with
                                                           | (head2',
                                                              uu____18461) ->
                                                               let uu____18486
                                                                 =
                                                                 let uu____18491
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu____18492
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu____18491,
                                                                   uu____18492) in
                                                               (match uu____18486
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
                                                                    let uu____18494
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____18494
                                                                    then
                                                                    let uu____18499
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____18501
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu____18503
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____18505
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18499
                                                                    uu____18501
                                                                    uu____18503
                                                                    uu____18505
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18510
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2694_18518
                                                                    = torig in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2694_18518.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2694_18518.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2694_18518.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2694_18518.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2694_18518.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2694_18518.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2694_18518.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2694_18518.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
                                                                    let uu____18520
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____18520
                                                                    then
                                                                    let uu____18525
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18525
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18530 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu____18542 =
                                             delta_depth_of_term env1 head1 in
                                           match uu____18542 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d in
                                         let treat_as_injective =
                                           let uu____18550 =
                                             let uu____18551 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu____18551.FStar_Syntax_Syntax.n in
                                           match uu____18550 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18556 -> false in
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
                                          | uu____18559 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18562 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t env1
                                           (let uu___2714_18598 = problem in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2714_18598.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2714_18598.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2714_18598.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2714_18598.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2714_18598.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2714_18598.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2714_18598.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2714_18598.FStar_TypeChecker_Common.rank)
                                            }) wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18674 = destruct_flex_t scrutinee wl1 in
             match uu____18674 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu____18685 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p in
                 (match uu____18685 with
                  | (xs, pat_term, uu____18701, uu____18702) ->
                      let uu____18707 =
                        FStar_List.fold_left
                          (fun uu____18730 ->
                             fun x ->
                               match uu____18730 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____18751 = copy_uvar uv [] t_x wl3 in
                                   (match uu____18751 with
                                    | (uu____18770, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu____18707 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu____18791 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic" in
                           (match uu____18791 with
                            | (prob, wl4) ->
                                let wl' =
                                  let uu___2755_18808 = wl4 in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2755_18808.wl_deferred_to_tac);
                                    ctr = (uu___2755_18808.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2755_18808.umax_heuristic_ok);
                                    tcenv = (uu___2755_18808.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2755_18808.repr_subcomp_allowed)
                                  } in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let uu____18819 = solve env1 wl' in
                                (match uu____18819 with
                                 | Success (uu____18822, defer_to_tac, imps)
                                     ->
                                     let wl'1 =
                                       let uu___2764_18826 = wl' in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2764_18826.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2764_18826.wl_deferred_to_tac);
                                         ctr = (uu___2764_18826.ctr);
                                         defer_ok =
                                           (uu___2764_18826.defer_ok);
                                         smt_ok = (uu___2764_18826.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2764_18826.umax_heuristic_ok);
                                         tcenv = (uu___2764_18826.tcenv);
                                         wl_implicits =
                                           (uu___2764_18826.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2764_18826.repr_subcomp_allowed)
                                       } in
                                     let uu____18827 = solve env1 wl'1 in
                                     (match uu____18827 with
                                      | Success
                                          (uu____18830, defer_to_tac', imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18834 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps') in
                                            FStar_Pervasives_Native.Some
                                              uu____18834))
                                      | Failed uu____18840 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18846 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None))))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu____18869 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu____18869
                 then
                   let uu____18874 = FStar_Syntax_Print.term_to_string t1 in
                   let uu____18876 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18874 uu____18876
                 else ());
                (let uu____18881 =
                   let uu____18902 =
                     let uu____18911 = FStar_Syntax_Util.unmeta t1 in
                     (s1, uu____18911) in
                   let uu____18918 =
                     let uu____18927 = FStar_Syntax_Util.unmeta t2 in
                     (s2, uu____18927) in
                   (uu____18902, uu____18918) in
                 match uu____18881 with
                 | ((uu____18957,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____18960;
                       FStar_Syntax_Syntax.vars = uu____18961;_}),
                    (s, t)) ->
                     let uu____19032 =
                       let uu____19034 = is_flex scrutinee in
                       Prims.op_Negation uu____19034 in
                     if uu____19032
                     then
                       ((let uu____19045 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____19045
                         then
                           let uu____19050 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19050
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19069 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19069
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19084 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19084
                           then
                             let uu____19089 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____19091 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19089 uu____19091
                           else ());
                          (let pat_discriminates uu___26_19116 =
                             match uu___26_19116 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19132;
                                  FStar_Syntax_Syntax.p = uu____19133;_},
                                FStar_Pervasives_Native.None, uu____19134) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19148;
                                  FStar_Syntax_Syntax.p = uu____19149;_},
                                FStar_Pervasives_Native.None, uu____19150) ->
                                 true
                             | uu____19177 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____19280 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____19280 with
                                       | (uu____19282, uu____19283, t') ->
                                           let uu____19301 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____19301 with
                                            | (FullMatch, uu____19313) ->
                                                true
                                            | (HeadMatch uu____19327,
                                               uu____19328) -> true
                                            | uu____19343 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____19380 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____19380
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19391 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____19391 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____19479, uu____19480)
                                       -> branches1
                                   | uu____19625 -> branches in
                                 let uu____19680 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____19689 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____19689 with
                                        | (p, uu____19693, uu____19694) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____19723 ->
                                      FStar_Util.Inr uu____19723) uu____19680))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19753 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____19753 with
                                | (p, uu____19762, e) ->
                                    ((let uu____19781 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____19781
                                      then
                                        let uu____19786 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____19788 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19786 uu____19788
                                      else ());
                                     (let uu____19793 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____19808 ->
                                           FStar_Util.Inr uu____19808)
                                        uu____19793)))))
                 | ((s, t),
                    (uu____19811,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____19814;
                       FStar_Syntax_Syntax.vars = uu____19815;_}))
                     ->
                     let uu____19884 =
                       let uu____19886 = is_flex scrutinee in
                       Prims.op_Negation uu____19886 in
                     if uu____19884
                     then
                       ((let uu____19897 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____19897
                         then
                           let uu____19902 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19902
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19921 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19921
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19936 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19936
                           then
                             let uu____19941 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____19943 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19941 uu____19943
                           else ());
                          (let pat_discriminates uu___26_19968 =
                             match uu___26_19968 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19984;
                                  FStar_Syntax_Syntax.p = uu____19985;_},
                                FStar_Pervasives_Native.None, uu____19986) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____20000;
                                  FStar_Syntax_Syntax.p = uu____20001;_},
                                FStar_Pervasives_Native.None, uu____20002) ->
                                 true
                             | uu____20029 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____20132 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____20132 with
                                       | (uu____20134, uu____20135, t') ->
                                           let uu____20153 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____20153 with
                                            | (FullMatch, uu____20165) ->
                                                true
                                            | (HeadMatch uu____20179,
                                               uu____20180) -> true
                                            | uu____20195 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____20232 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____20232
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20243 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____20243 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____20331, uu____20332)
                                       -> branches1
                                   | uu____20477 -> branches in
                                 let uu____20532 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____20541 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____20541 with
                                        | (p, uu____20545, uu____20546) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____20575 ->
                                      FStar_Util.Inr uu____20575) uu____20532))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20605 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____20605 with
                                | (p, uu____20614, e) ->
                                    ((let uu____20633 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____20633
                                      then
                                        let uu____20638 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____20640 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20638 uu____20640
                                      else ());
                                     (let uu____20645 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____20660 ->
                                           FStar_Util.Inr uu____20660)
                                        uu____20645)))))
                 | uu____20661 ->
                     ((let uu____20683 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu____20683
                       then
                         let uu____20688 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____20690 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20688 uu____20690
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____20736 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu____20736
            then
              let uu____20741 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____20743 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____20745 = FStar_Syntax_Print.term_to_string t1 in
              let uu____20747 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20741 uu____20743 uu____20745 uu____20747
            else ());
           (let uu____20752 = head_matches_delta env1 wl1 t1 t2 in
            match uu____20752 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu____20783, uu____20784) ->
                     let rec may_relate head =
                       let uu____20812 =
                         let uu____20813 = FStar_Syntax_Subst.compress head in
                         uu____20813.FStar_Syntax_Syntax.n in
                       match uu____20812 with
                       | FStar_Syntax_Syntax.Tm_name uu____20817 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20819 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20844 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv in
                           (match uu____20844 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20846 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20849
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20850 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t, uu____20853, uu____20854) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t, uu____20896) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t, uu____20902) ->
                           may_relate t
                       | uu____20907 -> false in
                     let uu____20909 =
                       try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu____20909 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20922 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig uu____20922
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None) ->
                          let uu____20932 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok in
                          if uu____20932
                          then
                            let uu____20935 =
                              guard_of_prob env1 wl1 problem t1 t2 in
                            (match uu____20935 with
                             | (guard, wl2) ->
                                 let uu____20942 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2 in
                                 solve env1 uu____20942)
                          else
                            (let uu____20945 =
                               mklstr
                                 (fun uu____20956 ->
                                    let uu____20957 =
                                      FStar_Syntax_Print.term_to_string head1 in
                                    let uu____20959 =
                                      let uu____20961 =
                                        let uu____20965 =
                                          delta_depth_of_term env1 head1 in
                                        FStar_Util.bind_opt uu____20965
                                          (fun x ->
                                             let uu____20972 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____20972) in
                                      FStar_Util.dflt "" uu____20961 in
                                    let uu____20977 =
                                      FStar_Syntax_Print.term_to_string head2 in
                                    let uu____20979 =
                                      let uu____20981 =
                                        let uu____20985 =
                                          delta_depth_of_term env1 head2 in
                                        FStar_Util.bind_opt uu____20985
                                          (fun x ->
                                             let uu____20992 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____20992) in
                                      FStar_Util.dflt "" uu____20981 in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20957 uu____20959 uu____20977
                                      uu____20979) in
                             giveup env1 uu____20945 orig))
                 | (HeadMatch (true), uu____20998) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____21013 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu____21013 with
                        | (guard, wl2) ->
                            let uu____21020 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu____21020)
                     else
                       (let uu____21023 =
                          mklstr
                            (fun uu____21030 ->
                               let uu____21031 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____21033 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____21031 uu____21033) in
                        giveup env1 uu____21023 orig)
                 | (uu____21036, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       (let uu___2946_21050 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2946_21050.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2946_21050.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2946_21050.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2946_21050.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2946_21050.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2946_21050.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2946_21050.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2946_21050.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____21077 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____21077
          then
            let uu____21080 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____21080
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu____21086 =
                let uu____21089 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____21089 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____21086 t1);
             (let uu____21108 =
                let uu____21111 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____21111 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____21108 t2);
             (let uu____21130 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu____21130
              then
                let uu____21134 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu____21136 =
                  let uu____21138 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu____21140 =
                    let uu____21142 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu____21142 in
                  Prims.op_Hat uu____21138 uu____21140 in
                let uu____21145 =
                  let uu____21147 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu____21149 =
                    let uu____21151 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu____21151 in
                  Prims.op_Hat uu____21147 uu____21149 in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21134 uu____21136 uu____21145
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21158, uu____21159) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21175, FStar_Syntax_Syntax.Tm_delayed uu____21176) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21192, uu____21193) ->
                  let uu____21220 =
                    let uu___2977_21221 = problem in
                    let uu____21222 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2977_21221.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21222;
                      FStar_TypeChecker_Common.relation =
                        (uu___2977_21221.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2977_21221.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2977_21221.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2977_21221.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2977_21221.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2977_21221.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2977_21221.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2977_21221.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21220 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21223, uu____21224) ->
                  let uu____21231 =
                    let uu___2983_21232 = problem in
                    let uu____21233 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2983_21232.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21233;
                      FStar_TypeChecker_Common.relation =
                        (uu___2983_21232.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2983_21232.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2983_21232.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2983_21232.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2983_21232.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2983_21232.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2983_21232.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2983_21232.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21231 wl
              | (uu____21234, FStar_Syntax_Syntax.Tm_ascribed uu____21235) ->
                  let uu____21262 =
                    let uu___2989_21263 = problem in
                    let uu____21264 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2989_21263.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2989_21263.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2989_21263.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21264;
                      FStar_TypeChecker_Common.element =
                        (uu___2989_21263.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2989_21263.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2989_21263.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2989_21263.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2989_21263.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2989_21263.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21262 wl
              | (uu____21265, FStar_Syntax_Syntax.Tm_meta uu____21266) ->
                  let uu____21273 =
                    let uu___2995_21274 = problem in
                    let uu____21275 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2995_21274.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2995_21274.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2995_21274.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21275;
                      FStar_TypeChecker_Common.element =
                        (uu___2995_21274.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2995_21274.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2995_21274.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2995_21274.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2995_21274.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2995_21274.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21273 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____21277),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu____21279)) ->
                  let uu____21288 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu____21288
              | (FStar_Syntax_Syntax.Tm_bvar uu____21289, uu____21290) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21292, FStar_Syntax_Syntax.Tm_bvar uu____21293) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___27_21363 =
                    match uu___27_21363 with
                    | [] -> c
                    | bs ->
                        let uu____21391 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu____21391 in
                  let uu____21402 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu____21402 with
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
                                    let uu____21551 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu____21551
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___28_21640 =
                    match uu___28_21640 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu____21682 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu____21682 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu____21827 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu____21828 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu____21827
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21828 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21830, uu____21831) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21862 -> true
                    | uu____21882 -> false in
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
                      (let uu____21942 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3097_21950 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3097_21950.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3097_21950.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3097_21950.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3097_21950.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3097_21950.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3097_21950.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3097_21950.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3097_21950.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3097_21950.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3097_21950.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3097_21950.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3097_21950.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3097_21950.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3097_21950.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3097_21950.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3097_21950.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3097_21950.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3097_21950.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3097_21950.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3097_21950.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3097_21950.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3097_21950.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3097_21950.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3097_21950.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3097_21950.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3097_21950.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3097_21950.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3097_21950.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3097_21950.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3097_21950.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3097_21950.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3097_21950.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3097_21950.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3097_21950.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3097_21950.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3097_21950.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3097_21950.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3097_21950.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3097_21950.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3097_21950.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3097_21950.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3097_21950.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3097_21950.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3097_21950.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____21942 with
                       | (uu____21955, ty, uu____21957) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____21966 =
                                 let uu____21967 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____21967.FStar_Syntax_Syntax.n in
                               match uu____21966 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21970 ->
                                   let uu____21977 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____21977
                               | uu____21978 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____21981 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____21981
                             then
                               let uu____21986 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____21988 =
                                 let uu____21990 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21990 in
                               let uu____21991 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21986 uu____21988 uu____21991
                             else ());
                            r1)) in
                  let uu____21996 =
                    let uu____22013 = maybe_eta t1 in
                    let uu____22020 = maybe_eta t2 in
                    (uu____22013, uu____22020) in
                  (match uu____21996 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3118_22062 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3118_22062.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3118_22062.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3118_22062.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3118_22062.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3118_22062.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3118_22062.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3118_22062.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3118_22062.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____22083 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22083
                       then
                         let uu____22086 = destruct_flex_t not_abs wl in
                         (match uu____22086 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3135_22103 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3135_22103.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3135_22103.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3135_22103.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3135_22103.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3135_22103.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3135_22103.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3135_22103.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3135_22103.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22106 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22106 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____22129 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22129
                       then
                         let uu____22132 = destruct_flex_t not_abs wl in
                         (match uu____22132 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3135_22149 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3135_22149.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3135_22149.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3135_22149.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3135_22149.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3135_22149.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3135_22149.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3135_22149.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3135_22149.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22152 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22152 orig))
                   | uu____22155 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22173, FStar_Syntax_Syntax.Tm_abs uu____22174) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22205 -> true
                    | uu____22225 -> false in
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
                      (let uu____22285 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3097_22293 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3097_22293.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3097_22293.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3097_22293.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3097_22293.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3097_22293.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3097_22293.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3097_22293.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3097_22293.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3097_22293.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3097_22293.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3097_22293.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3097_22293.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3097_22293.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3097_22293.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3097_22293.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3097_22293.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3097_22293.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3097_22293.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3097_22293.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3097_22293.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3097_22293.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3097_22293.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3097_22293.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3097_22293.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3097_22293.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3097_22293.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3097_22293.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3097_22293.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3097_22293.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3097_22293.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3097_22293.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3097_22293.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3097_22293.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3097_22293.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3097_22293.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3097_22293.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3097_22293.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3097_22293.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3097_22293.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3097_22293.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3097_22293.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3097_22293.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3097_22293.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3097_22293.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____22285 with
                       | (uu____22298, ty, uu____22300) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____22309 =
                                 let uu____22310 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____22310.FStar_Syntax_Syntax.n in
                               match uu____22309 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22313 ->
                                   let uu____22320 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____22320
                               | uu____22321 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____22324 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____22324
                             then
                               let uu____22329 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____22331 =
                                 let uu____22333 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22333 in
                               let uu____22334 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22329 uu____22331 uu____22334
                             else ());
                            r1)) in
                  let uu____22339 =
                    let uu____22356 = maybe_eta t1 in
                    let uu____22363 = maybe_eta t2 in
                    (uu____22356, uu____22363) in
                  (match uu____22339 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3118_22405 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3118_22405.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3118_22405.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3118_22405.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3118_22405.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3118_22405.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3118_22405.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3118_22405.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3118_22405.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____22426 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22426
                       then
                         let uu____22429 = destruct_flex_t not_abs wl in
                         (match uu____22429 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3135_22446 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3135_22446.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3135_22446.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3135_22446.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3135_22446.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3135_22446.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3135_22446.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3135_22446.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3135_22446.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22449 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22449 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____22472 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22472
                       then
                         let uu____22475 = destruct_flex_t not_abs wl in
                         (match uu____22475 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3135_22492 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3135_22492.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3135_22492.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3135_22492.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3135_22492.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3135_22492.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3135_22492.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3135_22492.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3135_22492.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22495 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22495 orig))
                   | uu____22498 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu____22528 =
                    let uu____22533 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu____22533 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ((let uu___3158_22561 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3158_22561.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3158_22561.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3160_22563 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3160_22563.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3160_22563.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22564, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ((let uu___3158_22579 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3158_22579.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3158_22579.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3160_22581 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3160_22581.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3160_22581.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22582 -> (x1, x2) in
                  (match uu____22528 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu____22601 = as_refinement false env t11 in
                       (match uu____22601 with
                        | (x12, phi11) ->
                            let uu____22609 = as_refinement false env t21 in
                            (match uu____22609 with
                             | (x22, phi21) ->
                                 ((let uu____22618 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu____22618
                                   then
                                     ((let uu____22623 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu____22625 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu____22627 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22623
                                         uu____22625 uu____22627);
                                      (let uu____22630 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu____22632 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu____22634 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22630
                                         uu____22632 uu____22634))
                                   else ());
                                  (let uu____22639 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu____22639 with
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
                                         let uu____22710 = imp phi13 phi23 in
                                         FStar_All.pipe_right uu____22710
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu____22722 =
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
                                         (let uu____22735 =
                                            let uu____22738 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22738 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22735
                                            (p_guard base_prob));
                                         (let uu____22757 =
                                            let uu____22760 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22760 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22757
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu____22779 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu____22779) in
                                       let has_uvars =
                                         (let uu____22784 =
                                            let uu____22786 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Util.set_is_empty
                                              uu____22786 in
                                          Prims.op_Negation uu____22784) ||
                                           (let uu____22790 =
                                              let uu____22792 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Util.set_is_empty
                                                uu____22792 in
                                            Prims.op_Negation uu____22790) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22796 =
                                           let uu____22801 =
                                             let uu____22810 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu____22810] in
                                           mk_t_problem wl1 uu____22801 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu____22796 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu____22833 =
                                                solve env1
                                                  (let uu___3203_22835 = wl2 in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3203_22835.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3203_22835.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3203_22835.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3203_22835.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3203_22835.tcenv);
                                                     wl_implicits =
                                                       (uu___3203_22835.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3203_22835.repr_subcomp_allowed)
                                                   }) in
                                              (match uu____22833 with
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
                                                   (uu____22850,
                                                    defer_to_tac,
                                                    uu____22852)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22857 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22857 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       let uu___3219_22866 =
                                                         wl3 in
                                                       {
                                                         attempting =
                                                           (uu___3219_22866.attempting);
                                                         wl_deferred =
                                                           (uu___3219_22866.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3219_22866.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3219_22866.defer_ok);
                                                         smt_ok =
                                                           (uu___3219_22866.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3219_22866.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3219_22866.tcenv);
                                                         wl_implicits =
                                                           (uu___3219_22866.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3219_22866.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac [] in
                                                     let uu____22869 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu____22869))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22872,
                 FStar_Syntax_Syntax.Tm_uvar uu____22873) ->
                  let uu____22898 = ensure_no_uvar_subst t1 wl in
                  (match uu____22898 with
                   | (t11, wl1) ->
                       let uu____22905 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____22905 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22914;
                    FStar_Syntax_Syntax.pos = uu____22915;
                    FStar_Syntax_Syntax.vars = uu____22916;_},
                  uu____22917),
                 FStar_Syntax_Syntax.Tm_uvar uu____22918) ->
                  let uu____22967 = ensure_no_uvar_subst t1 wl in
                  (match uu____22967 with
                   | (t11, wl1) ->
                       let uu____22974 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____22974 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22983,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22984;
                    FStar_Syntax_Syntax.pos = uu____22985;
                    FStar_Syntax_Syntax.vars = uu____22986;_},
                  uu____22987)) ->
                  let uu____23036 = ensure_no_uvar_subst t1 wl in
                  (match uu____23036 with
                   | (t11, wl1) ->
                       let uu____23043 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____23043 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23052;
                    FStar_Syntax_Syntax.pos = uu____23053;
                    FStar_Syntax_Syntax.vars = uu____23054;_},
                  uu____23055),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23056;
                    FStar_Syntax_Syntax.pos = uu____23057;
                    FStar_Syntax_Syntax.vars = uu____23058;_},
                  uu____23059)) ->
                  let uu____23132 = ensure_no_uvar_subst t1 wl in
                  (match uu____23132 with
                   | (t11, wl1) ->
                       let uu____23139 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____23139 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23148, uu____23149) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23162 = destruct_flex_t t1 wl in
                  (match uu____23162 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23169;
                    FStar_Syntax_Syntax.pos = uu____23170;
                    FStar_Syntax_Syntax.vars = uu____23171;_},
                  uu____23172),
                 uu____23173) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23210 = destruct_flex_t t1 wl in
                  (match uu____23210 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23217, FStar_Syntax_Syntax.Tm_uvar uu____23218) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23231, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23232;
                    FStar_Syntax_Syntax.pos = uu____23233;
                    FStar_Syntax_Syntax.vars = uu____23234;_},
                  uu____23235)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____23272,
                 FStar_Syntax_Syntax.Tm_arrow uu____23273) ->
                  solve_t' env
                    (let uu___3322_23301 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3322_23301.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3322_23301.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3322_23301.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3322_23301.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3322_23301.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3322_23301.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3322_23301.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3322_23301.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3322_23301.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23302;
                    FStar_Syntax_Syntax.pos = uu____23303;
                    FStar_Syntax_Syntax.vars = uu____23304;_},
                  uu____23305),
                 FStar_Syntax_Syntax.Tm_arrow uu____23306) ->
                  solve_t' env
                    (let uu___3322_23358 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3322_23358.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3322_23358.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3322_23358.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3322_23358.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3322_23358.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3322_23358.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3322_23358.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3322_23358.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3322_23358.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23359, FStar_Syntax_Syntax.Tm_uvar uu____23360) ->
                  let uu____23373 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23373
              | (uu____23374, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23375;
                    FStar_Syntax_Syntax.pos = uu____23376;
                    FStar_Syntax_Syntax.vars = uu____23377;_},
                  uu____23378)) ->
                  let uu____23415 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23415
              | (FStar_Syntax_Syntax.Tm_uvar uu____23416, uu____23417) ->
                  let uu____23430 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23430
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23431;
                    FStar_Syntax_Syntax.pos = uu____23432;
                    FStar_Syntax_Syntax.vars = uu____23433;_},
                  uu____23434),
                 uu____23435) ->
                  let uu____23472 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23472
              | (FStar_Syntax_Syntax.Tm_refine uu____23473, uu____23474) ->
                  let t21 =
                    let uu____23482 = base_and_refinement env t2 in
                    FStar_All.pipe_left force_refinement uu____23482 in
                  solve_t env
                    (let uu___3357_23508 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3357_23508.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3357_23508.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3357_23508.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3357_23508.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3357_23508.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3357_23508.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3357_23508.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3357_23508.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3357_23508.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23509, FStar_Syntax_Syntax.Tm_refine uu____23510) ->
                  let t11 =
                    let uu____23518 = base_and_refinement env t1 in
                    FStar_All.pipe_left force_refinement uu____23518 in
                  solve_t env
                    (let uu___3364_23544 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3364_23544.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3364_23544.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3364_23544.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3364_23544.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3364_23544.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3364_23544.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3364_23544.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3364_23544.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3364_23544.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match (s1, brs1),
                 FStar_Syntax_Syntax.Tm_match (s2, brs2)) ->
                  let by_smt uu____23626 =
                    let uu____23627 = guard_of_prob env wl problem t1 t2 in
                    match uu____23627 with
                    | (guard, wl1) ->
                        let uu____23634 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu____23634 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu____23853 = br1 in
                        (match uu____23853 with
                         | (p1, w1, uu____23882) ->
                             let uu____23899 = br2 in
                             (match uu____23899 with
                              | (p2, w2, uu____23922) ->
                                  let uu____23927 =
                                    let uu____23929 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu____23929 in
                                  if uu____23927
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23956 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu____23956 with
                                     | ((p11, w11, e1), s) ->
                                         let uu____23993 = br2 in
                                         (match uu____23993 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu____24026 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____24026 in
                                              let uu____24031 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____24062,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu____24083) ->
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
                                                    let uu____24142 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu____24142 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Util.bind_opt uu____24031
                                                (fun uu____24214 ->
                                                   match uu____24214 with
                                                   | (wprobs, wl2) ->
                                                       let uu____24251 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu____24251
                                                        with
                                                        | (prob, wl3) ->
                                                            ((let uu____24272
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu____24272
                                                              then
                                                                let uu____24277
                                                                  =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu____24279
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24277
                                                                  uu____24279
                                                              else ());
                                                             (let uu____24285
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Util.bind_opt
                                                                uu____24285
                                                                (fun
                                                                   uu____24321
                                                                   ->
                                                                   match uu____24321
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
                    | uu____24450 -> FStar_Pervasives_Native.None in
                  let uu____24491 = solve_branches wl brs1 brs2 in
                  (match uu____24491 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24517 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu____24517 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu____24544 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu____24544 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu____24578 =
                                FStar_List.map
                                  (fun uu____24590 ->
                                     match uu____24590 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu____24578 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu____24599 =
                              let uu____24600 =
                                let uu____24601 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1 in
                                attempt uu____24601
                                  (let uu___3463_24609 = wl3 in
                                   {
                                     attempting =
                                       (uu___3463_24609.attempting);
                                     wl_deferred =
                                       (uu___3463_24609.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3463_24609.wl_deferred_to_tac);
                                     ctr = (uu___3463_24609.ctr);
                                     defer_ok = (uu___3463_24609.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3463_24609.umax_heuristic_ok);
                                     tcenv = (uu___3463_24609.tcenv);
                                     wl_implicits =
                                       (uu___3463_24609.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3463_24609.repr_subcomp_allowed)
                                   }) in
                              solve env uu____24600 in
                            (match uu____24599 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24615 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24624 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu____24624 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24627, uu____24628) ->
                  let head1 =
                    let uu____24652 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24652
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24698 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24698
                      FStar_Pervasives_Native.fst in
                  ((let uu____24744 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24744
                    then
                      let uu____24748 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24750 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24752 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24748 uu____24750 uu____24752
                    else ());
                   (let no_free_uvars t =
                      (let uu____24766 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24766) &&
                        (let uu____24770 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24770) in
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
                      let uu____24789 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24789 = FStar_Syntax_Util.Equal in
                    let uu____24790 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24790
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24794 = equal t1 t2 in
                         (if uu____24794
                          then
                            let uu____24797 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24797
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24802 =
                            let uu____24809 = equal t1 t2 in
                            if uu____24809
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24822 = mk_eq2 wl env orig t1 t2 in
                               match uu____24822 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24802 with
                          | (guard, wl1) ->
                              let uu____24843 = solve_prob orig guard [] wl1 in
                              solve env uu____24843))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24846, uu____24847) ->
                  let head1 =
                    let uu____24855 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24855
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24901 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24901
                      FStar_Pervasives_Native.fst in
                  ((let uu____24947 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24947
                    then
                      let uu____24951 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24953 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24955 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24951 uu____24953 uu____24955
                    else ());
                   (let no_free_uvars t =
                      (let uu____24969 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24969) &&
                        (let uu____24973 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24973) in
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
                      let uu____24992 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24992 = FStar_Syntax_Util.Equal in
                    let uu____24993 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24993
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24997 = equal t1 t2 in
                         (if uu____24997
                          then
                            let uu____25000 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25000
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25005 =
                            let uu____25012 = equal t1 t2 in
                            if uu____25012
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25025 = mk_eq2 wl env orig t1 t2 in
                               match uu____25025 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25005 with
                          | (guard, wl1) ->
                              let uu____25046 = solve_prob orig guard [] wl1 in
                              solve env uu____25046))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____25049, uu____25050) ->
                  let head1 =
                    let uu____25052 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25052
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25098 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25098
                      FStar_Pervasives_Native.fst in
                  ((let uu____25144 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25144
                    then
                      let uu____25148 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25150 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25152 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25148 uu____25150 uu____25152
                    else ());
                   (let no_free_uvars t =
                      (let uu____25166 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25166) &&
                        (let uu____25170 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25170) in
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
                      let uu____25189 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25189 = FStar_Syntax_Util.Equal in
                    let uu____25190 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25190
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25194 = equal t1 t2 in
                         (if uu____25194
                          then
                            let uu____25197 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25197
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25202 =
                            let uu____25209 = equal t1 t2 in
                            if uu____25209
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25222 = mk_eq2 wl env orig t1 t2 in
                               match uu____25222 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25202 with
                          | (guard, wl1) ->
                              let uu____25243 = solve_prob orig guard [] wl1 in
                              solve env uu____25243))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25246, uu____25247) ->
                  let head1 =
                    let uu____25249 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25249
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25295 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25295
                      FStar_Pervasives_Native.fst in
                  ((let uu____25341 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25341
                    then
                      let uu____25345 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25347 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25349 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25345 uu____25347 uu____25349
                    else ());
                   (let no_free_uvars t =
                      (let uu____25363 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25363) &&
                        (let uu____25367 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25367) in
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
                      let uu____25386 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25386 = FStar_Syntax_Util.Equal in
                    let uu____25387 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25387
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25391 = equal t1 t2 in
                         (if uu____25391
                          then
                            let uu____25394 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25394
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25399 =
                            let uu____25406 = equal t1 t2 in
                            if uu____25406
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25419 = mk_eq2 wl env orig t1 t2 in
                               match uu____25419 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25399 with
                          | (guard, wl1) ->
                              let uu____25440 = solve_prob orig guard [] wl1 in
                              solve env uu____25440))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25443, uu____25444) ->
                  let head1 =
                    let uu____25446 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25446
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25486 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25486
                      FStar_Pervasives_Native.fst in
                  ((let uu____25526 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25526
                    then
                      let uu____25530 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25532 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25534 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25530 uu____25532 uu____25534
                    else ());
                   (let no_free_uvars t =
                      (let uu____25548 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25548) &&
                        (let uu____25552 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25552) in
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
                      let uu____25571 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25571 = FStar_Syntax_Util.Equal in
                    let uu____25572 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25572
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25576 = equal t1 t2 in
                         (if uu____25576
                          then
                            let uu____25579 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25579
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25584 =
                            let uu____25591 = equal t1 t2 in
                            if uu____25591
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25604 = mk_eq2 wl env orig t1 t2 in
                               match uu____25604 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25584 with
                          | (guard, wl1) ->
                              let uu____25625 = solve_prob orig guard [] wl1 in
                              solve env uu____25625))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25628, uu____25629) ->
                  let head1 =
                    let uu____25647 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25647
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25687 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25687
                      FStar_Pervasives_Native.fst in
                  ((let uu____25727 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25727
                    then
                      let uu____25731 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25733 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25735 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25731 uu____25733 uu____25735
                    else ());
                   (let no_free_uvars t =
                      (let uu____25749 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25749) &&
                        (let uu____25753 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25753) in
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
                      let uu____25772 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25772 = FStar_Syntax_Util.Equal in
                    let uu____25773 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25773
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25777 = equal t1 t2 in
                         (if uu____25777
                          then
                            let uu____25780 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25780
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25785 =
                            let uu____25792 = equal t1 t2 in
                            if uu____25792
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25805 = mk_eq2 wl env orig t1 t2 in
                               match uu____25805 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25785 with
                          | (guard, wl1) ->
                              let uu____25826 = solve_prob orig guard [] wl1 in
                              solve env uu____25826))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25829, FStar_Syntax_Syntax.Tm_match uu____25830) ->
                  let head1 =
                    let uu____25854 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25854
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25894 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25894
                      FStar_Pervasives_Native.fst in
                  ((let uu____25934 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25934
                    then
                      let uu____25938 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25940 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25942 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25938 uu____25940 uu____25942
                    else ());
                   (let no_free_uvars t =
                      (let uu____25956 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25956) &&
                        (let uu____25960 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25960) in
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
                      let uu____25979 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25979 = FStar_Syntax_Util.Equal in
                    let uu____25980 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25980
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25984 = equal t1 t2 in
                         (if uu____25984
                          then
                            let uu____25987 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25987
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25992 =
                            let uu____25999 = equal t1 t2 in
                            if uu____25999
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26012 = mk_eq2 wl env orig t1 t2 in
                               match uu____26012 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25992 with
                          | (guard, wl1) ->
                              let uu____26033 = solve_prob orig guard [] wl1 in
                              solve env uu____26033))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26036, FStar_Syntax_Syntax.Tm_uinst uu____26037) ->
                  let head1 =
                    let uu____26045 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26045
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26085 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26085
                      FStar_Pervasives_Native.fst in
                  ((let uu____26125 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26125
                    then
                      let uu____26129 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26131 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26133 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26129 uu____26131 uu____26133
                    else ());
                   (let no_free_uvars t =
                      (let uu____26147 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26147) &&
                        (let uu____26151 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26151) in
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
                      let uu____26170 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26170 = FStar_Syntax_Util.Equal in
                    let uu____26171 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26171
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26175 = equal t1 t2 in
                         (if uu____26175
                          then
                            let uu____26178 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26178
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26183 =
                            let uu____26190 = equal t1 t2 in
                            if uu____26190
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26203 = mk_eq2 wl env orig t1 t2 in
                               match uu____26203 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26183 with
                          | (guard, wl1) ->
                              let uu____26224 = solve_prob orig guard [] wl1 in
                              solve env uu____26224))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26227, FStar_Syntax_Syntax.Tm_name uu____26228) ->
                  let head1 =
                    let uu____26230 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26230
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26270 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26270
                      FStar_Pervasives_Native.fst in
                  ((let uu____26310 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26310
                    then
                      let uu____26314 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26316 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26318 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26314 uu____26316 uu____26318
                    else ());
                   (let no_free_uvars t =
                      (let uu____26332 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26332) &&
                        (let uu____26336 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26336) in
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
                      let uu____26355 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26355 = FStar_Syntax_Util.Equal in
                    let uu____26356 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26356
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26360 = equal t1 t2 in
                         (if uu____26360
                          then
                            let uu____26363 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26363
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26368 =
                            let uu____26375 = equal t1 t2 in
                            if uu____26375
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26388 = mk_eq2 wl env orig t1 t2 in
                               match uu____26388 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26368 with
                          | (guard, wl1) ->
                              let uu____26409 = solve_prob orig guard [] wl1 in
                              solve env uu____26409))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26412, FStar_Syntax_Syntax.Tm_constant uu____26413) ->
                  let head1 =
                    let uu____26415 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26415
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26455 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26455
                      FStar_Pervasives_Native.fst in
                  ((let uu____26495 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26495
                    then
                      let uu____26499 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26501 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26503 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26499 uu____26501 uu____26503
                    else ());
                   (let no_free_uvars t =
                      (let uu____26517 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26517) &&
                        (let uu____26521 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26521) in
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
                      let uu____26540 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26540 = FStar_Syntax_Util.Equal in
                    let uu____26541 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26541
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26545 = equal t1 t2 in
                         (if uu____26545
                          then
                            let uu____26548 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26548
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26553 =
                            let uu____26560 = equal t1 t2 in
                            if uu____26560
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26573 = mk_eq2 wl env orig t1 t2 in
                               match uu____26573 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26553 with
                          | (guard, wl1) ->
                              let uu____26594 = solve_prob orig guard [] wl1 in
                              solve env uu____26594))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26597, FStar_Syntax_Syntax.Tm_fvar uu____26598) ->
                  let head1 =
                    let uu____26600 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26600
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26646 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26646
                      FStar_Pervasives_Native.fst in
                  ((let uu____26692 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26692
                    then
                      let uu____26696 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26698 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26700 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26696 uu____26698 uu____26700
                    else ());
                   (let no_free_uvars t =
                      (let uu____26714 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26714) &&
                        (let uu____26718 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26718) in
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
                      let uu____26737 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26737 = FStar_Syntax_Util.Equal in
                    let uu____26738 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26738
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26742 = equal t1 t2 in
                         (if uu____26742
                          then
                            let uu____26745 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26745
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26750 =
                            let uu____26757 = equal t1 t2 in
                            if uu____26757
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26770 = mk_eq2 wl env orig t1 t2 in
                               match uu____26770 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26750 with
                          | (guard, wl1) ->
                              let uu____26791 = solve_prob orig guard [] wl1 in
                              solve env uu____26791))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26794, FStar_Syntax_Syntax.Tm_app uu____26795) ->
                  let head1 =
                    let uu____26813 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26813
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26853 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26853
                      FStar_Pervasives_Native.fst in
                  ((let uu____26893 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26893
                    then
                      let uu____26897 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26899 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26901 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26897 uu____26899 uu____26901
                    else ());
                   (let no_free_uvars t =
                      (let uu____26915 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26915) &&
                        (let uu____26919 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26919) in
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
                      let uu____26938 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26938 = FStar_Syntax_Util.Equal in
                    let uu____26939 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26939
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26943 = equal t1 t2 in
                         (if uu____26943
                          then
                            let uu____26946 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26946
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26951 =
                            let uu____26958 = equal t1 t2 in
                            if uu____26958
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26971 = mk_eq2 wl env orig t1 t2 in
                               match uu____26971 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26951 with
                          | (guard, wl1) ->
                              let uu____26992 = solve_prob orig guard [] wl1 in
                              solve env uu____26992))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu____26995,
                 FStar_Syntax_Syntax.Tm_let uu____26996) ->
                  let uu____27023 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu____27023
                  then
                    let uu____27026 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu____27026
                  else
                    (let uu____27029 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu____27029 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____27032, uu____27033) ->
                  let uu____27047 =
                    let uu____27053 =
                      let uu____27055 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____27057 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____27059 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____27061 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27055 uu____27057 uu____27059 uu____27061 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27053) in
                  FStar_Errors.raise_error uu____27047
                    t1.FStar_Syntax_Syntax.pos
              | (uu____27065, FStar_Syntax_Syntax.Tm_let uu____27066) ->
                  let uu____27080 =
                    let uu____27086 =
                      let uu____27088 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____27090 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____27092 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____27094 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27088 uu____27090 uu____27092 uu____27094 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27086) in
                  FStar_Errors.raise_error uu____27080
                    t1.FStar_Syntax_Syntax.pos
              | uu____27098 ->
                  let uu____27103 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu____27103 orig))))
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
          (let uu____27169 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____27169
           then
             let uu____27174 =
               let uu____27176 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu____27176 in
             let uu____27177 =
               let uu____27179 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu____27179 in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27174 uu____27177
           else ());
          (let uu____27183 =
             let uu____27185 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu____27185 in
           if uu____27183
           then
             let uu____27188 =
               mklstr
                 (fun uu____27195 ->
                    let uu____27196 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu____27198 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27196 uu____27198) in
             giveup env uu____27188 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27220 =
                  mklstr
                    (fun uu____27227 ->
                       let uu____27228 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu____27230 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27228 uu____27230) in
                giveup env uu____27220 orig)
             else
               (let uu____27235 =
                  FStar_List.fold_left2
                    (fun uu____27256 ->
                       fun u1 ->
                         fun u2 ->
                           match uu____27256 with
                           | (univ_sub_probs, wl1) ->
                               let uu____27277 =
                                 let uu____27282 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange in
                                 let uu____27283 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange in
                                 sub_prob wl1 uu____27282
                                   FStar_TypeChecker_Common.EQ uu____27283
                                   "effect universes" in
                               (match uu____27277 with
                                | (p, wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu____27235 with
                | (univ_sub_probs, wl1) ->
                    let uu____27303 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu____27303 with
                     | (ret_sub_prob, wl2) ->
                         let uu____27311 =
                           FStar_List.fold_right2
                             (fun uu____27348 ->
                                fun uu____27349 ->
                                  fun uu____27350 ->
                                    match (uu____27348, uu____27349,
                                            uu____27350)
                                    with
                                    | ((a1, uu____27394), (a2, uu____27396),
                                       (arg_sub_probs, wl3)) ->
                                        let uu____27429 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu____27429 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu____27311 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu____27456 =
                                  let uu____27459 =
                                    let uu____27462 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd) in
                                    FStar_List.append arg_sub_probs
                                      uu____27462 in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27459 in
                                FStar_List.append univ_sub_probs uu____27456 in
                              let guard =
                                let guard =
                                  let uu____27484 =
                                    FStar_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu____27484 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f in
                              let wl4 =
                                let uu___3616_27493 = wl3 in
                                {
                                  attempting = (uu___3616_27493.attempting);
                                  wl_deferred = (uu___3616_27493.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3616_27493.wl_deferred_to_tac);
                                  ctr = (uu___3616_27493.ctr);
                                  defer_ok = (uu___3616_27493.defer_ok);
                                  smt_ok = (uu___3616_27493.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3616_27493.umax_heuristic_ok);
                                  tcenv = (uu___3616_27493.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3616_27493.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu____27495 = attempt sub_probs wl5 in
                              solve env uu____27495)))) in
        let solve_layered_sub c11 c21 =
          (let uu____27508 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu____27508
           then
             let uu____27513 =
               let uu____27515 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____27515
                 FStar_Syntax_Print.comp_to_string in
             let uu____27517 =
               let uu____27519 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____27519
                 FStar_Syntax_Print.comp_to_string in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27513 uu____27517
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let subcomp_name =
               let uu____27530 =
                 let uu____27532 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____27532 FStar_Ident.string_of_id in
               let uu____27534 =
                 let uu____27536 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____27536 FStar_Ident.string_of_id in
               FStar_Util.format2 "%s <: %s" uu____27530 uu____27534 in
             let lift_c1 edge =
               let uu____27553 =
                 let uu____27558 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                 FStar_All.pipe_right uu____27558
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env) in
               FStar_All.pipe_right uu____27553
                 (fun uu____27575 ->
                    match uu____27575 with
                    | (c, g) ->
                        let uu____27586 =
                          FStar_Syntax_Util.comp_to_comp_typ c in
                        (uu____27586, g)) in
             let uu____27587 =
               let uu____27599 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name in
               match uu____27599 with
               | FStar_Pervasives_Native.None ->
                   let uu____27613 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name in
                   (match uu____27613 with
                    | FStar_Pervasives_Native.None ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____27632 = lift_c1 edge in
                        (match uu____27632 with
                         | (c12, g_lift) ->
                             let uu____27650 =
                               let uu____27653 =
                                 let uu____27654 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env) in
                                 FStar_All.pipe_right uu____27654
                                   FStar_Syntax_Util.get_stronger_vc_combinator in
                               FStar_All.pipe_right uu____27653
                                 (fun ts ->
                                    let uu____27660 =
                                      let uu____27661 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs in
                                      FStar_All.pipe_right uu____27661
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____27660
                                      (fun uu____27672 ->
                                         FStar_Pervasives_Native.Some
                                           uu____27672)) in
                             (c12, g_lift, uu____27650, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____27678 =
                     let uu____27681 =
                       let uu____27682 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs in
                       FStar_All.pipe_right uu____27682
                         FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____27681
                       (fun uu____27693 ->
                          FStar_Pervasives_Native.Some uu____27693) in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____27678,
                     true) in
             match uu____27587 with
             | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____27709 =
                     mklstr
                       (fun uu____27716 ->
                          let uu____27717 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name in
                          let uu____27719 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____27717 uu____27719) in
                   giveup env uu____27709 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must in
                    let wl1 =
                      let uu___3651_27728 = wl in
                      {
                        attempting = (uu___3651_27728.attempting);
                        wl_deferred = (uu___3651_27728.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3651_27728.wl_deferred_to_tac);
                        ctr = (uu___3651_27728.ctr);
                        defer_ok = (uu___3651_27728.defer_ok);
                        smt_ok = (uu___3651_27728.smt_ok);
                        umax_heuristic_ok =
                          (uu___3651_27728.umax_heuristic_ok);
                        tcenv = (uu___3651_27728.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3651_27728.repr_subcomp_allowed)
                      } in
                    let uu____27729 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____27754 =
                             let uu____27755 = FStar_Syntax_Subst.compress t in
                             uu____27755.FStar_Syntax_Syntax.n in
                           match uu____27754 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____27759 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1, uu____27774)
                               -> is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1, uu____27780) ->
                               is_uvar t1
                           | uu____27805 -> false in
                         FStar_List.fold_right2
                           (fun uu____27839 ->
                              fun uu____27840 ->
                                fun uu____27841 ->
                                  match (uu____27839, uu____27840,
                                          uu____27841)
                                  with
                                  | ((a1, uu____27885), (a2, uu____27887),
                                     (is_sub_probs, wl2)) ->
                                      let uu____27920 = is_uvar a1 in
                                      if uu____27920
                                      then
                                        ((let uu____27930 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns") in
                                          if uu____27930
                                          then
                                            let uu____27935 =
                                              FStar_Syntax_Print.term_to_string
                                                a1 in
                                            let uu____27937 =
                                              FStar_Syntax_Print.term_to_string
                                                a2 in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____27935 uu____27937
                                          else ());
                                         (let uu____27942 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar" in
                                          match uu____27942 with
                                          | (p, wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                    match uu____27729 with
                    | (is_sub_probs, wl2) ->
                        let uu____27970 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type" in
                        (match uu____27970 with
                         | (ret_sub_prob, wl3) ->
                             let stronger_t_shape_error s =
                               let uu____27987 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name in
                               let uu____27989 =
                                 FStar_Syntax_Print.term_to_string stronger_t in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____27987 s uu____27989 in
                             let uu____27992 =
                               let uu____28021 =
                                 let uu____28022 =
                                   FStar_Syntax_Subst.compress stronger_t in
                                 uu____28022.FStar_Syntax_Syntax.n in
                               match uu____28021 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____28082 =
                                     FStar_Syntax_Subst.open_comp bs c in
                                   (match uu____28082 with
                                    | (bs', c3) ->
                                        let a = FStar_List.hd bs' in
                                        let bs1 = FStar_List.tail bs' in
                                        let uu____28145 =
                                          let uu____28164 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one)) in
                                          FStar_All.pipe_right uu____28164
                                            (fun uu____28268 ->
                                               match uu____28268 with
                                               | (l1, l2) ->
                                                   let uu____28341 =
                                                     FStar_List.hd l2 in
                                                   (l1, uu____28341)) in
                                        (match uu____28145 with
                                         | (rest_bs, f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____28446 ->
                                   let uu____28447 =
                                     let uu____28453 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders" in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____28453) in
                                   FStar_Errors.raise_error uu____28447 r in
                             (match uu____27992 with
                              | (a_b, rest_bs, f_b, stronger_c) ->
                                  let uu____28529 =
                                    let uu____28536 =
                                      let uu____28537 =
                                        let uu____28538 =
                                          let uu____28545 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst in
                                          (uu____28545,
                                            (c21.FStar_Syntax_Syntax.result_typ)) in
                                        FStar_Syntax_Syntax.NT uu____28538 in
                                      [uu____28537] in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____28536
                                      (fun b ->
                                         let uu____28561 =
                                           FStar_Syntax_Print.binder_to_string
                                             b in
                                         let uu____28563 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name in
                                         let uu____28565 =
                                           FStar_Range.string_of_range r in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____28561 uu____28563
                                           uu____28565) r in
                                  (match uu____28529 with
                                   | (rest_bs_uvars, g_uvars) ->
                                       let wl4 =
                                         let uu___3716_28575 = wl3 in
                                         {
                                           attempting =
                                             (uu___3716_28575.attempting);
                                           wl_deferred =
                                             (uu___3716_28575.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3716_28575.wl_deferred_to_tac);
                                           ctr = (uu___3716_28575.ctr);
                                           defer_ok =
                                             (uu___3716_28575.defer_ok);
                                           smt_ok = (uu___3716_28575.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3716_28575.umax_heuristic_ok);
                                           tcenv = (uu___3716_28575.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3716_28575.repr_subcomp_allowed)
                                         } in
                                       let substs =
                                         FStar_List.map2
                                           (fun b ->
                                              fun t ->
                                                let uu____28600 =
                                                  let uu____28607 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst in
                                                  (uu____28607, t) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____28600) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars) in
                                       let uu____28624 =
                                         let f_sort_is =
                                           let uu____28634 =
                                             let uu____28637 =
                                               let uu____28638 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____28638.FStar_Syntax_Syntax.sort in
                                             let uu____28647 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name in
                                             let uu____28649 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type" in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____28637 uu____28647 r
                                               uu____28649 in
                                           FStar_All.pipe_right uu____28634
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs)) in
                                         let uu____28656 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_List.fold_left2
                                           (fun uu____28692 ->
                                              fun f_sort_i ->
                                                fun c1_i ->
                                                  match uu____28692 with
                                                  | (ps, wl5) ->
                                                      ((let uu____28714 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns") in
                                                        if uu____28714
                                                        then
                                                          let uu____28719 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i in
                                                          let uu____28721 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____28719
                                                            uu____28721
                                                        else ());
                                                       (let uu____28726 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1" in
                                                        match uu____28726
                                                        with
                                                        | (p, wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____28656 in
                                       (match uu____28624 with
                                        | (f_sub_probs, wl5) ->
                                            let stronger_ct =
                                              let uu____28751 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs) in
                                              FStar_All.pipe_right
                                                uu____28751
                                                FStar_Syntax_Util.comp_to_comp_typ in
                                            let uu____28752 =
                                              let g_sort_is =
                                                let uu____28762 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name in
                                                let uu____28764 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr" in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____28762 r uu____28764 in
                                              let uu____28767 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst) in
                                              FStar_List.fold_left2
                                                (fun uu____28803 ->
                                                   fun g_sort_i ->
                                                     fun c2_i ->
                                                       match uu____28803 with
                                                       | (ps, wl6) ->
                                                           ((let uu____28825
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                             if uu____28825
                                                             then
                                                               let uu____28830
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i in
                                                               let uu____28832
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____28830
                                                                 uu____28832
                                                             else ());
                                                            (let uu____28837
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2" in
                                                             match uu____28837
                                                             with
                                                             | (p, wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____28767 in
                                            (match uu____28752 with
                                             | (g_sub_probs, wl6) ->
                                                 let fml =
                                                   let uu____28864 =
                                                     let uu____28869 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                     let uu____28870 =
                                                       let uu____28871 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                       FStar_Pervasives_Native.fst
                                                         uu____28871 in
                                                     (uu____28869,
                                                       uu____28870) in
                                                   match uu____28864 with
                                                   | (u, wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange in
                                                 let sub_probs =
                                                   let uu____28899 =
                                                     let uu____28902 =
                                                       let uu____28905 =
                                                         let uu____28908 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____28908 in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____28905 in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____28902 in
                                                   ret_sub_prob ::
                                                     uu____28899 in
                                                 let guard =
                                                   let guard =
                                                     let uu____28932 =
                                                       FStar_List.map p_guard
                                                         sub_probs in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____28932 in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                       -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f in
                                                 let wl7 =
                                                   let uu____28943 =
                                                     let uu____28946 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml in
                                                     FStar_All.pipe_left
                                                       (fun uu____28949 ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____28949)
                                                       uu____28946 in
                                                   solve_prob orig
                                                     uu____28943 [] wl6 in
                                                 let uu____28950 =
                                                   attempt sub_probs wl7 in
                                                 solve env uu____28950))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu____28978 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____28980 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu____28980]
               | x -> x in
             let c12 =
               let uu___3774_28983 = c11 in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3774_28983.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3774_28983.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3774_28983.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3774_28983.FStar_Syntax_Syntax.flags)
               } in
             let uu____28984 =
               let uu____28989 =
                 FStar_All.pipe_right
                   (let uu___3777_28991 = c12 in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3777_28991.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3777_28991.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3777_28991.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3777_28991.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____28989
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env) in
             FStar_All.pipe_right uu____28984
               (fun uu____29005 ->
                  match uu____29005 with
                  | (c, g) ->
                      let uu____29012 =
                        let uu____29014 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu____29014 in
                      if uu____29012
                      then
                        let uu____29017 =
                          let uu____29023 =
                            let uu____29025 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu____29027 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____29025 uu____29027 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____29023) in
                        FStar_Errors.raise_error uu____29017 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu____29033 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____29036 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name in
                 Prims.op_Negation uu____29036))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name) in
           if uu____29033
           then
             let uu____29039 =
               mklstr
                 (fun uu____29046 ->
                    let uu____29047 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____29049 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____29047 uu____29049) in
             giveup env uu____29039 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_29060 ->
                        match uu___29_29060 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu____29065 -> false)) in
              let uu____29067 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu____29097)::uu____29098,
                   (wp2, uu____29100)::uu____29101) -> (wp1, wp2)
                | uu____29174 ->
                    let uu____29199 =
                      let uu____29205 =
                        let uu____29207 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu____29209 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____29207 uu____29209 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____29205) in
                    FStar_Errors.raise_error uu____29199
                      env.FStar_TypeChecker_Env.range in
              match uu____29067 with
              | (wpc1, wpc2) ->
                  let uu____29219 = FStar_Util.physical_equality wpc1 wpc2 in
                  if uu____29219
                  then
                    let uu____29222 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu____29222 wl
                  else
                    (let uu____29226 =
                       let uu____29233 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.must uu____29233 in
                     match uu____29226 with
                     | (c2_decl, qualifiers) ->
                         let uu____29254 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu____29254
                         then
                           let c1_repr =
                             let uu____29261 =
                               let uu____29262 =
                                 let uu____29263 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu____29263 in
                               let uu____29264 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____29262 uu____29264 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____29261 in
                           let c2_repr =
                             let uu____29267 =
                               let uu____29268 =
                                 FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu____29269 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____29268 uu____29269 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____29267 in
                           let uu____29271 =
                             let uu____29276 =
                               let uu____29278 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu____29280 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____29278 uu____29280 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____29276 in
                           (match uu____29271 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu____29286 = attempt [prob] wl2 in
                                solve env uu____29286)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____29306 = lift_c1 () in
                                   FStar_All.pipe_right uu____29306
                                     (fun ct ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu____29329 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____29329
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu____29339 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu____29339 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu____29346 =
                                       let uu____29347 =
                                         let uu____29364 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu____29367 =
                                           let uu____29378 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu____29378; wpc1_2] in
                                         (uu____29364, uu____29367) in
                                       FStar_Syntax_Syntax.Tm_app uu____29347 in
                                     FStar_Syntax_Syntax.mk uu____29346 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu____29427 =
                                      let uu____29428 =
                                        let uu____29445 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu____29448 =
                                          let uu____29459 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____29468 =
                                            let uu____29479 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu____29479; wpc1_2] in
                                          uu____29459 :: uu____29468 in
                                        (uu____29445, uu____29448) in
                                      FStar_Syntax_Syntax.Tm_app uu____29428 in
                                    FStar_Syntax_Syntax.mk uu____29427 r)) in
                            (let uu____29533 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____29533
                             then
                               let uu____29538 =
                                 let uu____29540 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string
                                   uu____29540 in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____29538
                             else ());
                            (let uu____29544 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu____29544 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu____29553 =
                                     let uu____29556 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_All.pipe_left
                                       (fun uu____29559 ->
                                          FStar_Pervasives_Native.Some
                                            uu____29559) uu____29556 in
                                   solve_prob orig uu____29553 [] wl1 in
                                 let uu____29560 = attempt [base_prob] wl2 in
                                 solve env uu____29560))))) in
        let uu____29561 = FStar_Util.physical_equality c1 c2 in
        if uu____29561
        then
          let uu____29564 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____29564
        else
          ((let uu____29568 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____29568
            then
              let uu____29573 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____29575 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29573
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29575
            else ());
           (let uu____29580 =
              let uu____29589 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____29592 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____29589, uu____29592) in
            match uu____29580 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____29610),
                    FStar_Syntax_Syntax.Total (t2, uu____29612)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29629 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29629 wl
                 | (FStar_Syntax_Syntax.GTotal uu____29631,
                    FStar_Syntax_Syntax.Total uu____29632) ->
                     let uu____29649 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu____29649 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____29653),
                    FStar_Syntax_Syntax.Total (t2, uu____29655)) ->
                     let uu____29672 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29672 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____29675),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29677)) ->
                     let uu____29694 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29694 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____29697),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29699)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29716 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29716 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____29719),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29721)) ->
                     let uu____29738 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu____29738 orig
                 | (FStar_Syntax_Syntax.GTotal uu____29741,
                    FStar_Syntax_Syntax.Comp uu____29742) ->
                     let uu____29751 =
                       let uu___3901_29754 = problem in
                       let uu____29757 =
                         let uu____29758 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29758 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3901_29754.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29757;
                         FStar_TypeChecker_Common.relation =
                           (uu___3901_29754.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3901_29754.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3901_29754.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3901_29754.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3901_29754.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3901_29754.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3901_29754.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3901_29754.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29751 wl
                 | (FStar_Syntax_Syntax.Total uu____29759,
                    FStar_Syntax_Syntax.Comp uu____29760) ->
                     let uu____29769 =
                       let uu___3901_29772 = problem in
                       let uu____29775 =
                         let uu____29776 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29776 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3901_29772.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29775;
                         FStar_TypeChecker_Common.relation =
                           (uu___3901_29772.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3901_29772.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3901_29772.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3901_29772.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3901_29772.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3901_29772.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3901_29772.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3901_29772.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29769 wl
                 | (FStar_Syntax_Syntax.Comp uu____29777,
                    FStar_Syntax_Syntax.GTotal uu____29778) ->
                     let uu____29787 =
                       let uu___3913_29790 = problem in
                       let uu____29793 =
                         let uu____29794 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29794 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3913_29790.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3913_29790.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3913_29790.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29793;
                         FStar_TypeChecker_Common.element =
                           (uu___3913_29790.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3913_29790.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3913_29790.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3913_29790.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3913_29790.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3913_29790.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29787 wl
                 | (FStar_Syntax_Syntax.Comp uu____29795,
                    FStar_Syntax_Syntax.Total uu____29796) ->
                     let uu____29805 =
                       let uu___3913_29808 = problem in
                       let uu____29811 =
                         let uu____29812 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29812 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3913_29808.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3913_29808.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3913_29808.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29811;
                         FStar_TypeChecker_Common.element =
                           (uu___3913_29808.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3913_29808.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3913_29808.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3913_29808.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3913_29808.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3913_29808.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29805 wl
                 | (FStar_Syntax_Syntax.Comp uu____29813,
                    FStar_Syntax_Syntax.Comp uu____29814) ->
                     let uu____29815 =
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
                     if uu____29815
                     then
                       let uu____29818 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____29818 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29825 =
                            let uu____29830 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu____29830
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29839 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____29840 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____29839, uu____29840)) in
                          match uu____29825 with
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
                           (let uu____29848 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____29848
                            then
                              let uu____29853 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu____29855 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29853 uu____29855
                            else ());
                           (let uu____29860 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu____29860
                            then solve_layered_sub c12 c22
                            else
                              (let uu____29865 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu____29865 with
                               | FStar_Pervasives_Native.None ->
                                   let uu____29868 =
                                     mklstr
                                       (fun uu____29875 ->
                                          let uu____29876 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu____29878 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____29876 uu____29878) in
                                   giveup env uu____29868 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu____29889 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_All.pipe_right uu____29889 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____29939 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____29939 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____29964 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29995 ->
                match uu____29995 with
                | (u1, u2) ->
                    let uu____30003 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____30005 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____30003 uu____30005)) in
      FStar_All.pipe_right uu____29964 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial, [], (uu____30042, [])) when
          let uu____30069 = FStar_Options.print_implicits () in
          Prims.op_Negation uu____30069 -> "{}"
      | uu____30072 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____30099 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu____30099
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu____30130 =
              FStar_List.map
                (fun uu____30144 ->
                   match uu____30144 with
                   | (msg, x) ->
                       let uu____30155 =
                         let uu____30157 = prob_to_string env x in
                         Prims.op_Hat ": " uu____30157 in
                       Prims.op_Hat msg uu____30155) defs in
            FStar_All.pipe_right uu____30130 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____30167 = carry g.FStar_TypeChecker_Common.deferred in
          let uu____30169 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu____30171 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30167 uu____30169 uu____30171 imps
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
                  let uu____30228 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu____30228
                  then
                    let uu____30236 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu____30238 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30236
                      (rel_to_string rel) uu____30238
                  else "TOP" in
                let uu____30244 =
                  new_problem wl env lhs rel rhs elt loc reason in
                match uu____30244 with
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
              let uu____30304 =
                let uu____30307 = FStar_TypeChecker_Env.get_range env in
                FStar_All.pipe_left
                  (fun uu____30310 ->
                     FStar_Pervasives_Native.Some uu____30310) uu____30307 in
              FStar_Syntax_Syntax.new_bv uu____30304 t1 in
            let uu____30311 =
              let uu____30316 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30316 in
            match uu____30311 with | (p, wl1) -> (p, x, wl1)
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
        (let uu____30388 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu____30388
         then
           let uu____30393 =
             FStar_Common.string_of_list
               (fun p -> FStar_Util.string_of_int (p_pid p)) probs.attempting in
           FStar_Util.print1 "solving problems %s {\n" uu____30393
         else ());
        (let uu____30400 =
           FStar_Util.record_time (fun uu____30407 -> solve env probs) in
         match uu____30400 with
         | (sol, ms) ->
             ((let uu____30421 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu____30421
               then
                 let uu____30426 = FStar_Util.string_of_int ms in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30426
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu____30442 =
                     FStar_Util.record_time
                       (fun uu____30449 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu____30442 with
                    | ((), ms1) ->
                        ((let uu____30462 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu____30462
                          then
                            let uu____30467 = FStar_Util.string_of_int ms1 in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30467
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu____30481 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu____30481
                     then
                       let uu____30488 = explain env d s in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30488
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
          ((let uu____30516 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____30516
            then
              let uu____30521 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30521
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu____30529 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____30529
             then
               let uu____30534 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30534
             else ());
            (let f2 =
               let uu____30540 =
                 let uu____30541 = FStar_Syntax_Util.unmeta f1 in
                 uu____30541.FStar_Syntax_Syntax.n in
               match uu____30540 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30545 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___4033_30546 = g in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4033_30546.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4033_30546.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4033_30546.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4033_30546.FStar_TypeChecker_Common.implicits)
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
            let uu____30598 =
              let uu____30599 =
                let uu____30600 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30601 ->
                       FStar_TypeChecker_Common.NonTrivial uu____30601) in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30600;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu____30599 in
            FStar_All.pipe_left
              (fun uu____30608 -> FStar_Pervasives_Native.Some uu____30608)
              uu____30598
let with_guard_no_simp :
  'uuuuuu30618 .
    'uuuuuu30618 ->
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
            let uu____30667 =
              let uu____30668 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30669 ->
                     FStar_TypeChecker_Common.NonTrivial uu____30669) in
              {
                FStar_TypeChecker_Common.guard_f = uu____30668;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              } in
            FStar_Pervasives_Native.Some uu____30667
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
          (let uu____30702 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____30702
           then
             let uu____30707 = FStar_Syntax_Print.term_to_string t1 in
             let uu____30709 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30707
               uu____30709
           else ());
          (let uu____30714 =
             let uu____30719 = FStar_TypeChecker_Env.get_range env in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30719 in
           match uu____30714 with
           | (prob, wl) ->
               let g =
                 let uu____30727 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30737 -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____30727 in
               ((let uu____30759 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____30759
                 then
                   let uu____30764 =
                     FStar_Common.string_of_option (guard_to_string env) g in
                   FStar_Util.print1 "} res = %s\n" uu____30764
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
        let uu____30785 = try_teq true env t1 t2 in
        match uu____30785 with
        | FStar_Pervasives_Native.None ->
            ((let uu____30790 = FStar_TypeChecker_Env.get_range env in
              let uu____30791 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____30790 uu____30791);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30799 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____30799
              then
                let uu____30804 = FStar_Syntax_Print.term_to_string t1 in
                let uu____30806 = FStar_Syntax_Print.term_to_string t2 in
                let uu____30808 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30804
                  uu____30806 uu____30808
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
        (let uu____30832 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____30832
         then
           let uu____30837 = FStar_Syntax_Print.term_to_string t1 in
           let uu____30839 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30837
             uu____30839
         else ());
        (let uu____30844 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu____30844 with
         | (prob, x, wl) ->
             let g =
               let uu____30859 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30870 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____30859 in
             ((let uu____30892 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____30892
               then
                 let uu____30897 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30897
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30905 =
                     let uu____30906 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu____30906 g1 in
                   FStar_Pervasives_Native.Some uu____30905)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____30928 = FStar_TypeChecker_Env.get_range env in
          let uu____30929 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____30928 uu____30929
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
        (let uu____30958 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____30958
         then
           let uu____30963 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____30965 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30963 uu____30965
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30976 =
           let uu____30983 = FStar_TypeChecker_Env.get_range env in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30983 "sub_comp" in
         match uu____30976 with
         | (prob, wl) ->
             let wl1 =
               let uu___4106_30994 = wl in
               {
                 attempting = (uu___4106_30994.attempting);
                 wl_deferred = (uu___4106_30994.wl_deferred);
                 wl_deferred_to_tac = (uu___4106_30994.wl_deferred_to_tac);
                 ctr = (uu___4106_30994.ctr);
                 defer_ok = (uu___4106_30994.defer_ok);
                 smt_ok = (uu___4106_30994.smt_ok);
                 umax_heuristic_ok = (uu___4106_30994.umax_heuristic_ok);
                 tcenv = (uu___4106_30994.tcenv);
                 wl_implicits = (uu___4106_30994.wl_implicits);
                 repr_subcomp_allowed = true
               } in
             let prob1 = FStar_TypeChecker_Common.CProb prob in
             (def_check_prob "sub_comp" prob1;
              (let uu____30999 =
                 FStar_Util.record_time
                   (fun uu____31011 ->
                      let uu____31012 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____31023 -> FStar_Pervasives_Native.None) in
                      FStar_All.pipe_left (with_guard env prob1) uu____31012) in
               match uu____30999 with
               | (r, ms) ->
                   ((let uu____31055 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench") in
                     if uu____31055
                     then
                       let uu____31060 = FStar_Syntax_Print.comp_to_string c1 in
                       let uu____31062 = FStar_Syntax_Print.comp_to_string c2 in
                       let uu____31064 = FStar_Util.string_of_int ms in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____31060 uu____31062
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____31064
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
      fun uu____31102 ->
        match uu____31102 with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31145 =
                 let uu____31151 =
                   let uu____31153 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____31155 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31153 uu____31155 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31151) in
               let uu____31159 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____31145 uu____31159) in
            let equiv v v' =
              let uu____31172 =
                let uu____31177 = FStar_Syntax_Subst.compress_univ v in
                let uu____31178 = FStar_Syntax_Subst.compress_univ v' in
                (uu____31177, uu____31178) in
              match uu____31172 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31202 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v ->
                      let uu____31233 = FStar_Syntax_Subst.compress_univ v in
                      match uu____31233 with
                      | FStar_Syntax_Syntax.U_unif uu____31240 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31271 ->
                                    match uu____31271 with
                                    | (u, v') ->
                                        let uu____31280 = equiv v v' in
                                        if uu____31280
                                        then
                                          let uu____31285 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____31285 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____31306 -> [])) in
            let uu____31311 =
              let wl =
                let uu___4149_31315 = empty_worklist env in
                {
                  attempting = (uu___4149_31315.attempting);
                  wl_deferred = (uu___4149_31315.wl_deferred);
                  wl_deferred_to_tac = (uu___4149_31315.wl_deferred_to_tac);
                  ctr = (uu___4149_31315.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4149_31315.smt_ok);
                  umax_heuristic_ok = (uu___4149_31315.umax_heuristic_ok);
                  tcenv = (uu___4149_31315.tcenv);
                  wl_implicits = (uu___4149_31315.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4149_31315.repr_subcomp_allowed)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31334 ->
                      match uu____31334 with
                      | (lb, v) ->
                          let uu____31341 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu____31341 with
                           | USolved wl1 -> ()
                           | uu____31344 -> fail lb v))) in
            let rec check_ineq uu____31355 =
              match uu____31355 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu____31367) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____31395,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____31397,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____31410) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v1)))
                   | (uu____31418, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v2 -> check_ineq (u1, v2)))
                   | uu____31427 -> false) in
            let uu____31433 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31450 ->
                      match uu____31450 with
                      | (u, v) ->
                          let uu____31458 = check_ineq (u, v) in
                          if uu____31458
                          then true
                          else
                            ((let uu____31466 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____31466
                              then
                                let uu____31471 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____31473 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" uu____31471
                                  uu____31473
                              else ());
                             false))) in
            if uu____31433
            then ()
            else
              ((let uu____31483 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____31483
                then
                  ((let uu____31489 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31489);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31501 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31501))
                else ());
               (let uu____31514 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31514))
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
          let fail uu____31596 =
            match uu____31596 with
            | (d, s) ->
                let msg = explain env d s in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d) in
          let wl =
            let uu___4227_31623 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred in
            {
              attempting = (uu___4227_31623.attempting);
              wl_deferred = (uu___4227_31623.wl_deferred);
              wl_deferred_to_tac = (uu___4227_31623.wl_deferred_to_tac);
              ctr = (uu___4227_31623.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4227_31623.umax_heuristic_ok);
              tcenv = (uu___4227_31623.tcenv);
              wl_implicits = (uu___4227_31623.wl_implicits);
              repr_subcomp_allowed = (uu___4227_31623.repr_subcomp_allowed)
            } in
          (let uu____31626 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____31626
           then
             let uu____31631 = FStar_Util.string_of_bool defer_ok in
             let uu____31633 = wl_to_string wl in
             let uu____31635 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits) in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31631 uu____31633 uu____31635
           else ());
          (let g1 =
             let uu____31641 = solve_and_commit env wl fail in
             match uu____31641 with
             | FStar_Pervasives_Native.Some
                 (uu____31650::uu____31651, uu____31652, uu____31653) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred, defer_to_tac, imps) ->
                 let uu___4244_31687 = g in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4244_31687.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4244_31687.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31693 ->
                 failwith "Impossible: should have raised a failure already" in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1 in
            (let uu____31706 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook") in
             if uu____31706
             then
               let uu____31711 = guard_to_string env g2 in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____31711
             else ());
            (let uu___4252_31716 = g2 in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4252_31716.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4252_31716.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4252_31716.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4252_31716.FStar_TypeChecker_Common.implicits)
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
          (let uu____31812 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu____31812
           then
             let uu____31817 = guard_to_string env g in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31817
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g in
           let ret_g =
             let uu___4269_31824 = g1 in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4269_31824.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4269_31824.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4269_31824.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4269_31824.FStar_TypeChecker_Common.implicits)
             } in
           let uu____31825 =
             let uu____31827 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu____31827 in
           if uu____31825
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____31839 = FStar_TypeChecker_Env.get_range env in
                      let uu____31840 =
                        let uu____31842 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31842 in
                      FStar_Errors.diag uu____31839 uu____31840)
                   else ();
                   (let vc1 =
                      let uu____31848 =
                        let uu____31852 =
                          let uu____31854 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu____31854 in
                        FStar_Pervasives_Native.Some uu____31852 in
                      FStar_Profiling.profile
                        (fun uu____31857 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31848 "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu____31861 = FStar_TypeChecker_Env.get_range env in
                       let uu____31862 =
                         let uu____31864 =
                           FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31864 in
                       FStar_Errors.diag uu____31861 uu____31862)
                    else ();
                    (let uu____31870 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31870 "discharge_guard'" env vc1);
                    (let uu____31872 =
                       FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu____31872 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____31881 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____31882 =
                                 let uu____31884 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31884 in
                               FStar_Errors.diag uu____31881 uu____31882)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____31894 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____31895 =
                                 let uu____31897 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31897 in
                               FStar_Errors.diag uu____31894 uu____31895)
                            else ();
                            (let vcs =
                               let uu____31911 = FStar_Options.use_tactics () in
                               if uu____31911
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31933 ->
                                      (let uu____31935 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_All.pipe_left
                                         (fun uu____31937 -> ()) uu____31935);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31980 ->
                                               match uu____31980 with
                                               | (env1, goal, opts) ->
                                                   let uu____31996 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu____31996, opts)))))
                               else
                                 (let uu____32000 =
                                    let uu____32007 = FStar_Options.peek () in
                                    (env, vc2, uu____32007) in
                                  [uu____32000]) in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____32040 ->
                                     match uu____32040 with
                                     | (env1, goal, opts) ->
                                         let uu____32050 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu____32050 with
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
                                                 (let uu____32061 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____32062 =
                                                    let uu____32064 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu____32066 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____32064 uu____32066 in
                                                  FStar_Errors.diag
                                                    uu____32061 uu____32062)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____32073 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____32074 =
                                                    let uu____32076 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____32076 in
                                                  FStar_Errors.diag
                                                    uu____32073 uu____32074)
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
      let uu____32094 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____32094 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____32103 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____32103
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____32117 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____32117 with
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
        let uu____32147 = try_teq false env t1 t2 in
        match uu____32147 with
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
             let uu____32202 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu____32202 with
             | (ctx_u, r) ->
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                 let uu____32212 =
                   let uu____32213 = FStar_Syntax_Subst.compress t_norm in
                   uu____32213.FStar_Syntax_Syntax.n in
                 (match uu____32212 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu____32219 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____32219
                        (fun uu____32222 ->
                           FStar_Pervasives_Native.Some uu____32222)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____32224) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu____32229 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____32229
                        (fun uu____32232 ->
                           FStar_Pervasives_Native.Some uu____32232)
                  | uu____32233 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_List.fold_left
               (fun b ->
                  fun imp ->
                    let uu____32246 =
                      let uu____32248 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_All.pipe_right uu____32248 FStar_Util.is_none in
                    if uu____32246
                    then
                      let uu____32256 = imp_value imp in
                      match uu____32256 with
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
        let uu____32285 =
          if is_tac
          then (false, true)
          else
            (((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
                (Prims.op_Negation env.FStar_TypeChecker_Env.lax)), false) in
        match uu____32285 with
        | (must_total, forcelax) ->
            let rec unresolved ctx_u =
              let uu____32321 =
                FStar_Syntax_Unionfind.find
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
              match uu____32321 with
              | FStar_Pervasives_Native.Some r ->
                  (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                   | FStar_Pervasives_Native.None -> false
                   | FStar_Pervasives_Native.Some uu____32328 ->
                       let uu____32329 =
                         let uu____32330 = FStar_Syntax_Subst.compress r in
                         uu____32330.FStar_Syntax_Syntax.n in
                       (match uu____32329 with
                        | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____32335)
                            -> unresolved ctx_u'
                        | uu____32352 -> false))
              | FStar_Pervasives_Native.None -> true in
            let rec until_fixpoint acc implicits =
              let uu____32376 = acc in
              match uu____32376 with
              | (out, changed) ->
                  (match implicits with
                   | [] ->
                       if Prims.op_Negation changed
                       then
                         let uu____32387 =
                           try_solve_single_valued_implicits env is_tac out in
                         (match uu____32387 with
                          | (out1, changed1) ->
                              if changed1
                              then until_fixpoint ([], false) out1
                              else out1)
                       else until_fixpoint ([], false) out
                   | hd::tl ->
                       let uu____32410 = hd in
                       (match uu____32410 with
                        | { FStar_TypeChecker_Common.imp_reason = reason;
                            FStar_TypeChecker_Common.imp_uvar = ctx_u;
                            FStar_TypeChecker_Common.imp_tm = tm;
                            FStar_TypeChecker_Common.imp_range = r;_} ->
                            if
                              ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                = FStar_Syntax_Syntax.Allow_unresolved
                            then until_fixpoint (out, true) tl
                            else
                              (let uu____32421 = unresolved ctx_u in
                               if uu____32421
                               then
                                 match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                     (env_dyn, tau)) ->
                                     let env1 = FStar_Dyn.undyn env_dyn in
                                     ((let uu____32432 =
                                         FStar_TypeChecker_Env.debug env1
                                           (FStar_Options.Other "Tac") in
                                       if uu____32432
                                       then
                                         let uu____32436 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             ctx_u in
                                         FStar_Util.print1
                                           "Running tactic for meta-arg %s\n"
                                           uu____32436
                                       else ());
                                      (let t =
                                         env1.FStar_TypeChecker_Env.synth_hook
                                           env1
                                           (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                           tau in
                                       let extra =
                                         let uu____32445 =
                                           teq_nosmt env1 t tm in
                                         match uu____32445 with
                                         | FStar_Pervasives_Native.None ->
                                             failwith
                                               "resolve_implicits: unifying with an unresolved uvar failed?"
                                         | FStar_Pervasives_Native.Some g1 ->
                                             g1.FStar_TypeChecker_Common.implicits in
                                       let ctx_u1 =
                                         let uu___4414_32455 = ctx_u in
                                         {
                                           FStar_Syntax_Syntax.ctx_uvar_head
                                             =
                                             (uu___4414_32455.FStar_Syntax_Syntax.ctx_uvar_head);
                                           FStar_Syntax_Syntax.ctx_uvar_gamma
                                             =
                                             (uu___4414_32455.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                           FStar_Syntax_Syntax.ctx_uvar_binders
                                             =
                                             (uu___4414_32455.FStar_Syntax_Syntax.ctx_uvar_binders);
                                           FStar_Syntax_Syntax.ctx_uvar_typ =
                                             (uu___4414_32455.FStar_Syntax_Syntax.ctx_uvar_typ);
                                           FStar_Syntax_Syntax.ctx_uvar_reason
                                             =
                                             (uu___4414_32455.FStar_Syntax_Syntax.ctx_uvar_reason);
                                           FStar_Syntax_Syntax.ctx_uvar_should_check
                                             =
                                             (uu___4414_32455.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                           FStar_Syntax_Syntax.ctx_uvar_range
                                             =
                                             (uu___4414_32455.FStar_Syntax_Syntax.ctx_uvar_range);
                                           FStar_Syntax_Syntax.ctx_uvar_meta
                                             = FStar_Pervasives_Native.None
                                         } in
                                       let hd1 =
                                         let uu___4417_32457 = hd in
                                         {
                                           FStar_TypeChecker_Common.imp_reason
                                             =
                                             (uu___4417_32457.FStar_TypeChecker_Common.imp_reason);
                                           FStar_TypeChecker_Common.imp_uvar
                                             = ctx_u1;
                                           FStar_TypeChecker_Common.imp_tm =
                                             (uu___4417_32457.FStar_TypeChecker_Common.imp_tm);
                                           FStar_TypeChecker_Common.imp_range
                                             =
                                             (uu___4417_32457.FStar_TypeChecker_Common.imp_range)
                                         } in
                                       until_fixpoint (out, true)
                                         (FStar_List.append extra tl)))
                                 | uu____32460 ->
                                     until_fixpoint ((hd :: out), changed) tl
                               else
                                 if
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                     = FStar_Syntax_Syntax.Allow_untyped
                                 then until_fixpoint (out, true) tl
                                 else
                                   (let env1 =
                                      let uu___4422_32472 = env in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4422_32472.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4422_32472.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4422_32472.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4422_32472.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4422_32472.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4422_32472.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4422_32472.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4422_32472.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4422_32472.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4422_32472.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4422_32472.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4422_32472.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4422_32472.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4422_32472.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4422_32472.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4422_32472.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4422_32472.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4422_32472.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4422_32472.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___4422_32472.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4422_32472.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4422_32472.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4422_32472.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4422_32472.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4422_32472.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4422_32472.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4422_32472.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4422_32472.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4422_32472.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4422_32472.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4422_32472.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4422_32472.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4422_32472.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4422_32472.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4422_32472.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4422_32472.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4422_32472.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4422_32472.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4422_32472.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4422_32472.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4422_32472.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4422_32472.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4422_32472.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4422_32472.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4422_32472.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4422_32472.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    let tm1 =
                                      norm_with_steps
                                        "FStar.TypeChecker.Rel.norm_with_steps.8"
                                        [FStar_TypeChecker_Env.Beta] env1 tm in
                                    let env2 =
                                      if forcelax
                                      then
                                        let uu___4427_32477 = env1 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___4427_32477.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___4427_32477.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___4427_32477.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___4427_32477.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___4427_32477.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___4427_32477.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___4427_32477.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___4427_32477.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___4427_32477.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___4427_32477.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___4427_32477.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___4427_32477.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___4427_32477.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___4427_32477.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___4427_32477.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___4427_32477.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___4427_32477.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___4427_32477.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___4427_32477.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___4427_32477.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___4427_32477.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___4427_32477.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___4427_32477.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___4427_32477.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___4427_32477.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___4427_32477.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___4427_32477.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___4427_32477.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___4427_32477.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___4427_32477.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___4427_32477.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (uu___4427_32477.FStar_TypeChecker_Env.enable_defer_to_tac)
                                        }
                                      else env1 in
                                    (let uu____32482 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env2)
                                         (FStar_Options.Other "Rel") in
                                     if uu____32482
                                     then
                                       let uu____32487 =
                                         FStar_Syntax_Print.uvar_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                       let uu____32489 =
                                         FStar_Syntax_Print.term_to_string
                                           tm1 in
                                       let uu____32491 =
                                         FStar_Syntax_Print.term_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                       let uu____32493 =
                                         FStar_Range.string_of_range r in
                                       FStar_Util.print5
                                         "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                         uu____32487 uu____32489 uu____32491
                                         reason uu____32493
                                     else ());
                                    (let g1 =
                                       try
                                         (fun uu___4433_32500 ->
                                            match () with
                                            | () ->
                                                env2.FStar_TypeChecker_Env.check_type_of
                                                  must_total env2 tm1
                                                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                           ()
                                       with
                                       | e when FStar_Errors.handleable e ->
                                           ((let uu____32507 =
                                               let uu____32517 =
                                                 let uu____32525 =
                                                   let uu____32527 =
                                                     FStar_Syntax_Print.uvar_to_string
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu____32529 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2 tm1 in
                                                   let uu____32531 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                   FStar_Util.format3
                                                     "Failed while checking implicit %s set to %s of expected type %s"
                                                     uu____32527 uu____32529
                                                     uu____32531 in
                                                 (FStar_Errors.Error_BadImplicit,
                                                   uu____32525, r) in
                                               [uu____32517] in
                                             FStar_Errors.add_errors
                                               uu____32507);
                                            FStar_Exn.raise e) in
                                     let g' =
                                       let uu____32550 =
                                         discharge_guard'
                                           (FStar_Pervasives_Native.Some
                                              (fun uu____32561 ->
                                                 let uu____32562 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm1 in
                                                 let uu____32564 =
                                                   FStar_Range.string_of_range
                                                     r in
                                                 let uu____32566 =
                                                   FStar_Range.string_of_range
                                                     tm1.FStar_Syntax_Syntax.pos in
                                                 FStar_Util.format4
                                                   "%s (Introduced at %s for %s resolved at %s)"
                                                   uu____32562 uu____32564
                                                   reason uu____32566)) env2
                                           g1 true in
                                       match uu____32550 with
                                       | FStar_Pervasives_Native.Some g2 ->
                                           g2
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                                     until_fixpoint
                                       ((FStar_List.append
                                           g'.FStar_TypeChecker_Common.implicits
                                           out), true) tl))))) in
            let uu___4445_32574 = g in
            let uu____32575 =
              until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4445_32574.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4445_32574.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4445_32574.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4445_32574.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = uu____32575
            }
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu____32590 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____32590
       then
         let uu____32595 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32595
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
      (let uu____32625 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____32625
       then
         let uu____32630 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32630
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____32637 = discharge_guard env g2 in
           FStar_All.pipe_left (fun uu____32638 -> ()) uu____32637
       | imp::uu____32640 ->
           let uu____32643 =
             let uu____32649 =
               let uu____32651 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____32653 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____32651 uu____32653
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32649) in
           FStar_Errors.raise_error uu____32643
             imp.FStar_TypeChecker_Common.imp_range)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32673 = teq env t1 t2 in
        force_trivial_guard env uu____32673
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32692 = teq_nosmt env t1 t2 in
        match uu____32692 with
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
          (let uu____32728 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu____32728
           then
             let uu____32733 =
               let uu____32735 =
                 FStar_All.pipe_right reason FStar_Util.is_none in
               if uu____32735
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must in
             let uu____32752 = FStar_Syntax_Print.term_to_string t1 in
             let uu____32754 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____32733
               uu____32752 uu____32754
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___4483_32770 = FStar_TypeChecker_Common.trivial_guard in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4483_32770.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4483_32770.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4483_32770.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4483_32770.FStar_TypeChecker_Common.implicits)
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
        (let uu____32806 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____32806
         then
           let uu____32811 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____32813 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32811
             uu____32813
         else ());
        (let uu____32818 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____32818 with
         | (prob, x, wl) ->
             let g =
               let uu____32837 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32848 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____32837 in
             ((let uu____32870 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____32870
               then
                 let uu____32875 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____32877 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____32879 =
                   let uu____32881 = FStar_Util.must g in
                   guard_to_string env uu____32881 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32875 uu____32877 uu____32879
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
        let uu____32918 = check_subtyping env t1 t2 in
        match uu____32918 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____32937 =
              let uu____32938 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu____32938 g in
            FStar_Pervasives_Native.Some uu____32937
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32957 = check_subtyping env t1 t2 in
        match uu____32957 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____32976 =
              let uu____32977 =
                let uu____32978 = FStar_Syntax_Syntax.mk_binder x in
                [uu____32978] in
              FStar_TypeChecker_Env.close_guard env uu____32977 g in
            FStar_Pervasives_Native.Some uu____32976
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____33016 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____33016
         then
           let uu____33021 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____33023 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____33021
             uu____33023
         else ());
        (let uu____33028 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____33028 with
         | (prob, x, wl) ->
             let g =
               let uu____33043 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____33054 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____33043 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____33079 =
                      let uu____33080 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____33080] in
                    FStar_TypeChecker_Env.close_guard env uu____33079 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____33121 = subtype_nosmt env t1 t2 in
        match uu____33121 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)