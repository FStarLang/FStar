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
                 | uu____6719 -> out) FStar_Syntax_Syntax.no_names g in
        let uu____6720 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6784 ->
                  fun uu____6785 ->
                    match (uu____6784, uu____6785) with
                    | ((isect, isect_set), (x, imp)) ->
                        let uu____6888 =
                          let uu____6890 = FStar_Util.set_mem x v1_set in
                          FStar_All.pipe_left Prims.op_Negation uu____6890 in
                        if uu____6888
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort in
                           let uu____6924 =
                             FStar_Util.set_is_subset_of fvs isect_set in
                           if uu____6924
                           then
                             let uu____6941 = FStar_Util.set_add x isect_set in
                             (((x, imp) :: isect), uu____6941)
                           else (isect, isect_set))) ([], ctx_binders)) in
        match uu____6720 with | (isect, uu____6991) -> FStar_List.rev isect
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt ->
    fun xs ->
      fun src ->
        fun wl ->
          let uu____7039 =
            maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
              src.FStar_Syntax_Syntax.ctx_uvar_binders in
          match uu____7039 with
          | (pfx, (tgt_sfx, src_sfx)) ->
              let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx in
              let xs_i = intersect_binders g src_sfx xs in
              let new_typ =
                let uu____7062 =
                  FStar_Syntax_Syntax.mk_Total
                    src.FStar_Syntax_Syntax.ctx_uvar_typ in
                FStar_Syntax_Util.arrow xs_i uu____7062 in
              let uu____7065 =
                let uu____7072 =
                  let uu____7074 =
                    FStar_Syntax_Print.uvar_to_string
                      src.FStar_Syntax_Syntax.ctx_uvar_head in
                  Prims.op_Hat "restricted " uu____7074 in
                new_uvar uu____7072 wl src.FStar_Syntax_Syntax.ctx_uvar_range
                  g pfx new_typ src.FStar_Syntax_Syntax.ctx_uvar_should_check
                  src.FStar_Syntax_Syntax.ctx_uvar_meta in
              (match uu____7065 with
               | (uu____7077, src', wl1) ->
                   let xs_args =
                     let uu____7081 =
                       FStar_Syntax_Syntax.binders_to_names xs_i in
                     FStar_List.map FStar_Syntax_Syntax.as_arg uu____7081 in
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
  'uuuuuu7128 'uuuuuu7129 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu7128) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7129) Prims.list -> Prims.bool
  =
  fun v1 ->
    fun v2 ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7187 ->
              fun uu____7188 ->
                match (uu____7187, uu____7188) with
                | ((a, uu____7207), (b, uu____7209)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
let name_exists_in_binders :
  'uuuuuu7225 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7225) Prims.list -> Prims.bool
  =
  fun x ->
    fun bs ->
      FStar_Util.for_some
        (fun uu____7256 ->
           match uu____7256 with
           | (y, uu____7263) -> FStar_Syntax_Syntax.bv_eq x y) bs
let pat_vars :
  'uuuuuu7273 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7273) Prims.list ->
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
                   let uu____7435 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx) in
                   if uu____7435
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7468 -> FStar_Pervasives_Native.None) in
        aux [] args
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | MisMatch _0 -> true | uu____7520 -> false
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | MisMatch _0 -> _0
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | HeadMatch _0 -> true | uu____7564 -> false
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee -> match projectee with | HeadMatch _0 -> _0
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee ->
    match projectee with | FullMatch -> true | uu____7585 -> false
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7593 ->
    match uu___19_7593 with
    | MisMatch (d1, d2) ->
        let uu____7605 =
          let uu____7607 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1 in
          let uu____7609 =
            let uu____7611 =
              let uu____7613 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2 in
              Prims.op_Hat uu____7613 ")" in
            Prims.op_Hat ") (" uu____7611 in
          Prims.op_Hat uu____7607 uu____7609 in
        Prims.op_Hat "MisMatch (" uu____7605
    | HeadMatch u ->
        let uu____7620 = FStar_Util.string_of_bool u in
        Prims.op_Hat "HeadMatch " uu____7620
    | FullMatch -> "FullMatch"
let (head_match : match_result -> match_result) =
  fun uu___20_7629 ->
    match uu___20_7629 with
    | MisMatch (i, j) -> MisMatch (i, j)
    | HeadMatch (true) -> HeadMatch true
    | uu____7646 -> HeadMatch false
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env ->
    fun fv ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7661 =
            (let uu____7667 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule in
             let uu____7669 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             uu____7667 = uu____7669) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface) in
          if uu____7661 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7678 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____7678 with
           | FStar_Pervasives_Native.None ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7689 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7713 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7723 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7742 = FStar_Syntax_Util.unfold_lazy i in
          delta_depth_of_term env uu____7742
      | FStar_Syntax_Syntax.Tm_unknown -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7743 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7744 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7745 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7758 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7772 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu____7796) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____7802, uu____7803) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2, uu____7845) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7870;
             FStar_Syntax_Syntax.index = uu____7871;
             FStar_Syntax_Syntax.sort = t2;_},
           uu____7873)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7881 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7882 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7883 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7898 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7905 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7925 = fv_delta_depth env fv in
          FStar_Pervasives_Native.Some uu____7925
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
           { FStar_Syntax_Syntax.blob = uu____7944;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7945;
             FStar_Syntax_Syntax.ltyp = uu____7946;
             FStar_Syntax_Syntax.rng = uu____7947;_},
           uu____7948) ->
            let uu____7959 = FStar_Syntax_Util.unlazy t11 in
            head_matches env uu____7959 t21
        | (uu____7960, FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7961;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7962;
             FStar_Syntax_Syntax.ltyp = uu____7963;
             FStar_Syntax_Syntax.rng = uu____7964;_})
            ->
            let uu____7975 = FStar_Syntax_Util.unlazy t21 in
            head_matches env t11 uu____7975
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7978 = FStar_Syntax_Syntax.bv_eq x y in
            if uu____7978
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7989 = FStar_Syntax_Syntax.fv_eq f g in
            if uu____7989
            then FullMatch
            else
              (let uu____7994 =
                 let uu____8003 =
                   let uu____8006 = fv_delta_depth env f in
                   FStar_Pervasives_Native.Some uu____8006 in
                 let uu____8007 =
                   let uu____8010 = fv_delta_depth env g in
                   FStar_Pervasives_Native.Some uu____8010 in
                 (uu____8003, uu____8007) in
               MisMatch uu____7994)
        | (FStar_Syntax_Syntax.Tm_uinst (f, uu____8016),
           FStar_Syntax_Syntax.Tm_uinst (g, uu____8018)) ->
            let uu____8027 = head_matches env f g in
            FStar_All.pipe_right uu____8027 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify)) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify),
           uu____8028) -> HeadMatch true
        | (uu____8030, FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify)) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____8034 = FStar_Const.eq_const c d in
            if uu____8034
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar (uv, uu____8044),
           FStar_Syntax_Syntax.Tm_uvar (uv', uu____8046)) ->
            let uu____8079 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head in
            if uu____8079
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____8089),
           FStar_Syntax_Syntax.Tm_refine (y, uu____8091)) ->
            let uu____8100 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____8100 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x, uu____8102), uu____8103) ->
            let uu____8108 = head_matches env x.FStar_Syntax_Syntax.sort t21 in
            FStar_All.pipe_right uu____8108 head_match
        | (uu____8109, FStar_Syntax_Syntax.Tm_refine (x, uu____8111)) ->
            let uu____8116 = head_matches env t11 x.FStar_Syntax_Syntax.sort in
            FStar_All.pipe_right uu____8116 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8117,
           FStar_Syntax_Syntax.Tm_type uu____8118) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow uu____8120,
           FStar_Syntax_Syntax.Tm_arrow uu____8121) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app (head, uu____8152),
           FStar_Syntax_Syntax.Tm_app (head', uu____8154)) ->
            let uu____8203 = head_matches env head head' in
            FStar_All.pipe_right uu____8203 head_match
        | (FStar_Syntax_Syntax.Tm_app (head, uu____8205), uu____8206) ->
            let uu____8231 = head_matches env head t21 in
            FStar_All.pipe_right uu____8231 head_match
        | (uu____8232, FStar_Syntax_Syntax.Tm_app (head, uu____8234)) ->
            let uu____8259 = head_matches env t11 head in
            FStar_All.pipe_right uu____8259 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8260, FStar_Syntax_Syntax.Tm_let
           uu____8261) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match uu____8289,
           FStar_Syntax_Syntax.Tm_match uu____8290) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8336, FStar_Syntax_Syntax.Tm_abs
           uu____8337) -> HeadMatch true
        | uu____8375 ->
            let uu____8380 =
              let uu____8389 = delta_depth_of_term env t11 in
              let uu____8392 = delta_depth_of_term env t21 in
              (uu____8389, uu____8392) in
            MisMatch uu____8380
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
              let uu____8461 = unrefine env t in
              FStar_Syntax_Util.head_of uu____8461 in
            (let uu____8463 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____8463
             then
               let uu____8468 = FStar_Syntax_Print.term_to_string t in
               let uu____8470 = FStar_Syntax_Print.term_to_string head in
               FStar_Util.print2 "Head of %s is %s\n" uu____8468 uu____8470
             else ());
            (let uu____8475 =
               let uu____8476 = FStar_Syntax_Util.un_uinst head in
               uu____8476.FStar_Syntax_Syntax.n in
             match uu____8475 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8482 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                 (match uu____8482 with
                  | FStar_Pervasives_Native.None ->
                      ((let uu____8496 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta") in
                        if uu____8496
                        then
                          let uu____8501 =
                            FStar_Syntax_Print.term_to_string head in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8501
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8506 ->
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
                      let uu____8524 =
                        let uu____8526 = FStar_Syntax_Util.eq_tm t t' in
                        uu____8526 = FStar_Syntax_Util.Equal in
                      if uu____8524
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8533 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta") in
                          if uu____8533
                          then
                            let uu____8538 =
                              FStar_Syntax_Print.term_to_string t in
                            let uu____8540 =
                              FStar_Syntax_Print.term_to_string t' in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8538
                              uu____8540
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8545 -> FStar_Pervasives_Native.None) in
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
            (let uu____8697 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta") in
             if uu____8697
             then
               let uu____8702 = FStar_Syntax_Print.term_to_string t11 in
               let uu____8704 = FStar_Syntax_Print.term_to_string t21 in
               let uu____8706 = string_of_match_result r in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8702
                 uu____8704 uu____8706
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2 in
               let uu____8734 =
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
               match uu____8734 with
               | (t12, t22) -> aux retry (n_delta + Prims.int_one) t12 t22 in
             let reduce_both_and_try_again d r1 =
               let uu____8782 = FStar_TypeChecker_Common.decr_delta_depth d in
               match uu____8782 with
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
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8820),
                  uu____8821)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8842 =
                      let uu____8851 = maybe_inline t11 in
                      let uu____8854 = maybe_inline t21 in
                      (uu____8851, uu____8854) in
                    match uu____8842 with
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
                 (uu____8897, FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8898))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8919 =
                      let uu____8928 = maybe_inline t11 in
                      let uu____8931 = maybe_inline t21 in
                      (uu____8928, uu____8931) in
                    match uu____8919 with
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
             | MisMatch uu____8986 -> fail n_delta r t11 t21
             | uu____8995 -> success n_delta r t11 t21) in
          let r = aux true Prims.int_zero t1 t2 in
          (let uu____9010 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta") in
           if uu____9010
           then
             let uu____9015 = FStar_Syntax_Print.term_to_string t1 in
             let uu____9017 = FStar_Syntax_Print.term_to_string t2 in
             let uu____9019 =
               string_of_match_result (FStar_Pervasives_Native.fst r) in
             let uu____9027 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____9044 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must in
                  FStar_All.pipe_right uu____9044
                    (fun uu____9079 ->
                       match uu____9079 with
                       | (t11, t21) ->
                           let uu____9087 =
                             FStar_Syntax_Print.term_to_string t11 in
                           let uu____9089 =
                             let uu____9091 =
                               FStar_Syntax_Print.term_to_string t21 in
                             Prims.op_Hat "; " uu____9091 in
                           Prims.op_Hat uu____9087 uu____9089)) in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____9015 uu____9017 uu____9019 uu____9027
           else ());
          r
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders ->
    fun r ->
      let uu____9108 = FStar_Syntax_Util.type_u () in
      FStar_All.pipe_right uu____9108 FStar_Pervasives_Native.fst
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_9123 ->
    match uu___21_9123 with
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
      let uu___1267_9172 = p in
      let uu____9175 = whnf tcenv p.FStar_TypeChecker_Common.lhs in
      let uu____9176 = whnf tcenv p.FStar_TypeChecker_Common.rhs in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1267_9172.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9175;
        FStar_TypeChecker_Common.relation =
          (uu___1267_9172.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9176;
        FStar_TypeChecker_Common.element =
          (uu___1267_9172.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1267_9172.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1267_9172.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1267_9172.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1267_9172.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1267_9172.FStar_TypeChecker_Common.rank)
      }
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv ->
    fun p ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9191 = compress_tprob tcenv p1 in
          FStar_All.pipe_right uu____9191
            (fun uu____9196 -> FStar_TypeChecker_Common.TProb uu____9196)
      | FStar_TypeChecker_Common.CProb uu____9197 -> p
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv ->
    fun pr ->
      let prob =
        let uu____9220 = compress_prob tcenv pr in
        FStar_All.pipe_right uu____9220 maybe_invert_p in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9228 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs in
          (match uu____9228 with
           | (lh, lhs_args) ->
               let uu____9275 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs in
               (match uu____9275 with
                | (rh, rhs_args) ->
                    let uu____9322 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9335,
                         FStar_Syntax_Syntax.Tm_uvar uu____9336) ->
                          (match (lhs_args, rhs_args) with
                           | ([], []) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9425 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9452, uu____9453)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9468, FStar_Syntax_Syntax.Tm_uvar uu____9469)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9484,
                         FStar_Syntax_Syntax.Tm_arrow uu____9485) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1318_9515 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1318_9515.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1318_9515.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1318_9515.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1318_9515.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1318_9515.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1318_9515.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1318_9515.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1318_9515.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1318_9515.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9518,
                         FStar_Syntax_Syntax.Tm_type uu____9519) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1318_9535 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1318_9535.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1318_9535.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1318_9535.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1318_9535.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1318_9535.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1318_9535.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1318_9535.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1318_9535.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1318_9535.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type uu____9538,
                         FStar_Syntax_Syntax.Tm_uvar uu____9539) ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1318_9555 = tp in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1318_9555.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1318_9555.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1318_9555.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1318_9555.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1318_9555.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1318_9555.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1318_9555.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1318_9555.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1318_9555.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9558, FStar_Syntax_Syntax.Tm_uvar uu____9559)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9574, uu____9575)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9590, FStar_Syntax_Syntax.Tm_uvar uu____9591)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9606, uu____9607) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp) in
                    (match uu____9322 with
                     | (rank, tp1) ->
                         let uu____9620 =
                           FStar_All.pipe_right
                             (let uu___1338_9624 = tp1 in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1338_9624.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1338_9624.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1338_9624.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1338_9624.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1338_9624.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1338_9624.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1338_9624.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1338_9624.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1338_9624.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9627 ->
                                FStar_TypeChecker_Common.TProb uu____9627) in
                         (rank, uu____9620))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9631 =
            FStar_All.pipe_right
              (let uu___1342_9635 = cp in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1342_9635.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1342_9635.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1342_9635.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1342_9635.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1342_9635.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1342_9635.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1342_9635.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1342_9635.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1342_9635.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9638 -> FStar_TypeChecker_Common.CProb uu____9638) in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9631)
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl ->
    let rec aux uu____9698 probs =
      match uu____9698 with
      | (min_rank, min, out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some p,
                   FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9779 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9800 = rank wl.tcenv hd in
               (match uu____9800 with
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
                      (let uu____9861 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9866 = FStar_Option.get min_rank in
                            rank_less_than rank1 uu____9866) in
                       if uu____9861
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
          let uu____9939 = FStar_Syntax_Util.head_and_args t in
          match uu____9939 with
          | (hd, uu____9958) ->
              let uu____9983 =
                let uu____9984 = FStar_Syntax_Subst.compress hd in
                uu____9984.FStar_Syntax_Syntax.n in
              (match uu____9983 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu____9989) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____10024 ->
                           match uu____10024 with
                           | (y, uu____10033) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____10056 ->
                                       match uu____10056 with
                                       | (x, uu____10065) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____10070 -> false) in
        let uu____10072 = rank tcenv p in
        match uu____10072 with
        | (r, p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____10081 -> true
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
    match projectee with | UDeferred _0 -> true | uu____10162 -> false
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | UDeferred _0 -> _0
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | USolved _0 -> true | uu____10181 -> false
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee -> match projectee with | USolved _0 -> _0
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee ->
    match projectee with | UFailed _0 -> true | uu____10200 -> false
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee -> match projectee with | UFailed _0 -> _0
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s -> let uu____10217 = FStar_Thunk.mkv s in UFailed uu____10217
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s -> let uu____10232 = mklstr s in UFailed uu____10232
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
                        let uu____10283 = FStar_Syntax_Util.univ_kernel u3 in
                        match uu____10283 with
                        | (k, uu____10291) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10306 -> false)))
            | uu____10308 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u]) in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs ->
                      fun uv1 ->
                        let uu____10360 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2 -> FStar_Syntax_Util.eq_univs uv1 uv2)) in
                        if uu____10360 then uv1 :: uvs else uvs) []) in
            let filter =
              FStar_List.filter
                (fun u ->
                   let uu____10384 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u' -> FStar_Syntax_Util.eq_univs u u')) in
                   Prims.op_Negation uu____10384) in
            let uu____10391 = filter u12 in
            let uu____10394 = filter u22 in (uu____10391, uu____10394) in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10429 = filter_out_common_univs us1 us2 in
                   (match uu____10429 with
                    | (us11, us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13, u23::us23) ->
                                let uu____10489 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23 in
                                (match uu____10489 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10492 -> USolved wl1 in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10509 ->
                               let uu____10510 =
                                 FStar_Syntax_Print.univ_to_string u12 in
                               let uu____10512 =
                                 FStar_Syntax_Print.univ_to_string u22 in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10510 uu____10512))
               | (FStar_Syntax_Syntax.U_max us, u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10538 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____10538 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | (u', FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10564 =
                           really_solve_universe_eq pid_orig wl1 u u' in
                         (match uu____10564 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed) in
                   aux wl us
               | uu____10567 ->
                   ufailed_thunk
                     (fun uu____10578 ->
                        let uu____10579 =
                          FStar_Syntax_Print.univ_to_string u12 in
                        let uu____10581 =
                          FStar_Syntax_Print.univ_to_string u22 in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10579 uu____10581 msg)) in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10584, uu____10585) ->
              let uu____10587 =
                let uu____10589 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10591 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10589 uu____10591 in
              failwith uu____10587
          | (FStar_Syntax_Syntax.U_unknown, uu____10594) ->
              let uu____10595 =
                let uu____10597 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10599 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10597 uu____10599 in
              failwith uu____10595
          | (uu____10602, FStar_Syntax_Syntax.U_bvar uu____10603) ->
              let uu____10605 =
                let uu____10607 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10609 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10607 uu____10609 in
              failwith uu____10605
          | (uu____10612, FStar_Syntax_Syntax.U_unknown) ->
              let uu____10613 =
                let uu____10615 = FStar_Syntax_Print.univ_to_string u11 in
                let uu____10617 = FStar_Syntax_Print.univ_to_string u21 in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10615 uu____10617 in
              failwith uu____10613
          | (FStar_Syntax_Syntax.U_name x, FStar_Syntax_Syntax.U_name y) ->
              let uu____10622 =
                let uu____10624 = FStar_Ident.string_of_id x in
                let uu____10626 = FStar_Ident.string_of_id y in
                uu____10624 = uu____10626 in
              if uu____10622
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12, FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1, FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10657 = FStar_Syntax_Unionfind.univ_equiv v1 v2 in
              if uu____10657
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1, u) ->
              let u3 = norm_univ wl u in
              let uu____10676 = occurs_univ v1 u3 in
              if uu____10676
              then
                let uu____10679 =
                  let uu____10681 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____10683 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10681 uu____10683 in
                try_umax_components u11 u21 uu____10679
              else
                (let uu____10688 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____10688)
          | (u, FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u in
              let uu____10702 = occurs_univ v1 u3 in
              if uu____10702
              then
                let uu____10705 =
                  let uu____10707 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1) in
                  let uu____10709 = FStar_Syntax_Print.univ_to_string u3 in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10707 uu____10709 in
                try_umax_components u11 u21 uu____10705
              else
                (let uu____10714 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl in
                 USolved uu____10714)
          | (FStar_Syntax_Syntax.U_max uu____10715, uu____10716) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____10724 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____10724
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10730, FStar_Syntax_Syntax.U_max uu____10731) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11 in
                 let u22 = norm_univ wl u21 in
                 let uu____10739 = FStar_Syntax_Util.eq_univs u12 u22 in
                 if uu____10739
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ uu____10745,
             FStar_Syntax_Syntax.U_zero) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ uu____10747,
             FStar_Syntax_Syntax.U_name uu____10748) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_succ
             uu____10750) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_name
             uu____10752) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____10754,
             FStar_Syntax_Syntax.U_succ uu____10755) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name uu____10757,
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
      let uu____10864 = bc1 in
      match uu____10864 with
      | (bs1, mk_cod1) ->
          let uu____10908 = bc2 in
          (match uu____10908 with
           | (bs2, mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs, y::ys) ->
                     let uu____11019 = aux xs ys in
                     (match uu____11019 with
                      | ((xs1, xr), (ys1, yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs, ys) ->
                     let uu____11102 =
                       let uu____11109 = mk_cod1 xs in ([], uu____11109) in
                     let uu____11112 =
                       let uu____11119 = mk_cod2 ys in ([], uu____11119) in
                     (uu____11102, uu____11112) in
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
                  let uu____11188 = FStar_Syntax_Syntax.bv_to_name t in
                  FStar_Syntax_Util.mk_has_type t11 uu____11188 t21
              | FStar_Pervasives_Native.None ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11 in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11 in
                  let uu____11191 =
                    let uu____11192 = FStar_Syntax_Syntax.bv_to_name x in
                    FStar_Syntax_Util.mk_has_type t11 uu____11192 t21 in
                  FStar_Syntax_Util.mk_forall u_x x uu____11191 in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB ->
                let uu____11197 = has_type_guard t1 t2 in (uu____11197, wl)
            | FStar_TypeChecker_Common.SUBINV ->
                let uu____11198 = has_type_guard t2 t1 in (uu____11198, wl)
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_11205 ->
    match uu___22_11205 with
    | Flex (uu____11207, uu____11208, []) -> true
    | uu____11218 -> false
let (should_defer_flex_to_user_tac :
  FStar_TypeChecker_Env.env -> worklist -> flex_t -> Prims.bool) =
  fun env ->
    fun wl ->
      fun f ->
        let uu____11237 = f in
        match uu____11237 with
        | Flex (uu____11239, u, uu____11241) ->
            let b =
              FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                wl.tcenv u in
            ((let uu____11245 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "ResolveImplicitsHook") in
              if uu____11245
              then
                let uu____11250 =
                  FStar_Syntax_Print.ctx_uvar_to_string_no_reason u in
                let uu____11252 = FStar_Util.string_of_bool b in
                FStar_Util.print2
                  "Rel.should_defer_flex_to_user_tac for %s returning %s\n"
                  uu____11250 uu____11252
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
      let uu____11280 = f in
      match uu____11280 with
      | Flex
          (uu____11287,
           { FStar_Syntax_Syntax.ctx_uvar_head = uu____11288;
             FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11289;
             FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
             FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
             FStar_Syntax_Syntax.ctx_uvar_reason = uu____11292;
             FStar_Syntax_Syntax.ctx_uvar_should_check = uu____11293;
             FStar_Syntax_Syntax.ctx_uvar_range = uu____11294;
             FStar_Syntax_Syntax.ctx_uvar_meta = uu____11295;_},
           args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11361 ->
                 match uu____11361 with
                 | (y, uu____11370) -> FStar_Syntax_Syntax.bv_eq x y) bs in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([], []) ->
                let uu____11524 =
                  let uu____11539 =
                    let uu____11542 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____11542 in
                  ((FStar_List.rev pat_binders), uu____11539) in
                FStar_Pervasives_Native.Some uu____11524
            | (uu____11575, []) ->
                let uu____11606 =
                  let uu____11621 =
                    let uu____11624 = FStar_Syntax_Syntax.mk_Total t_res in
                    FStar_Syntax_Util.arrow formals uu____11624 in
                  ((FStar_List.rev pat_binders), uu____11621) in
                FStar_Pervasives_Native.Some uu____11606
            | ((formal, formal_imp)::formals1, (a, a_imp)::args2) ->
                let uu____11715 =
                  let uu____11716 = FStar_Syntax_Subst.compress a in
                  uu____11716.FStar_Syntax_Syntax.n in
                (match uu____11715 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11736 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders) in
                     if uu____11736
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1683_11766 = x in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1683_11766.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1683_11766.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          } in
                        let subst =
                          let uu____11770 =
                            let uu____11771 =
                              let uu____11778 =
                                FStar_Syntax_Syntax.bv_to_name x1 in
                              (formal, uu____11778) in
                            FStar_Syntax_Syntax.NT uu____11771 in
                          [uu____11770] in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1 in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res in
                        aux
                          (((let uu___1689_11794 = x1 in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1689_11794.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1689_11794.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11795 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([], args2) ->
                let uu____11835 =
                  let uu____11842 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res in
                  FStar_Syntax_Util.arrow_formals uu____11842 in
                (match uu____11835 with
                 | (more_formals, t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11901 ->
                          aux pat_binders more_formals t_res1 args2)) in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11926 ->
               let uu____11927 = FStar_Syntax_Util.arrow_formals t_hd in
               (match uu____11927 with
                | (formals, t_res) -> aux [] formals t_res args))
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env ->
    fun probs ->
      (let uu____12259 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel") in
       if uu____12259
       then
         let uu____12264 = wl_to_string probs in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12264
       else ());
      (let uu____12270 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace") in
       if uu____12270
       then
         let uu____12275 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12275
       else ());
      (let uu____12280 = next_prob probs in
       match uu____12280 with
       | FStar_Pervasives_Native.Some (hd, tl, rank1) ->
           let probs1 =
             let uu___1716_12307 = probs in
             {
               attempting = tl;
               wl_deferred = (uu___1716_12307.wl_deferred);
               wl_deferred_to_tac = (uu___1716_12307.wl_deferred_to_tac);
               ctr = (uu___1716_12307.ctr);
               defer_ok = (uu___1716_12307.defer_ok);
               smt_ok = (uu___1716_12307.smt_ok);
               umax_heuristic_ok = (uu___1716_12307.umax_heuristic_ok);
               tcenv = (uu___1716_12307.tcenv);
               wl_implicits = (uu___1716_12307.wl_implicits);
               repr_subcomp_allowed = (uu___1716_12307.repr_subcomp_allowed)
             } in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12316 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs in
                 if uu____12316
                 then
                   let uu____12319 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1 in
                   solve env uu____12319
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
                           (let uu___1728_12331 = tp in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1728_12331.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1728_12331.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1728_12331.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1728_12331.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1728_12331.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1728_12331.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1728_12331.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1728_12331.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1728_12331.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12351 =
                  let uu____12358 = as_deferred probs.wl_deferred_to_tac in
                  ([], uu____12358, (probs.wl_implicits)) in
                Success uu____12351
            | uu____12364 ->
                let uu____12374 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12439 ->
                          match uu____12439 with
                          | (c, uu____12449, uu____12450) -> c < probs.ctr)) in
                (match uu____12374 with
                 | (attempt1, rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12498 =
                            let uu____12505 = as_deferred probs.wl_deferred in
                            let uu____12506 =
                              as_deferred probs.wl_deferred_to_tac in
                            (uu____12505, uu____12506, (probs.wl_implicits)) in
                          Success uu____12498
                      | uu____12507 ->
                          let uu____12517 =
                            let uu___1742_12518 = probs in
                            let uu____12519 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12540 ->
                                      match uu____12540 with
                                      | (uu____12548, uu____12549, y) -> y)) in
                            {
                              attempting = uu____12519;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1742_12518.wl_deferred_to_tac);
                              ctr = (uu___1742_12518.ctr);
                              defer_ok = (uu___1742_12518.defer_ok);
                              smt_ok = (uu___1742_12518.smt_ok);
                              umax_heuristic_ok =
                                (uu___1742_12518.umax_heuristic_ok);
                              tcenv = (uu___1742_12518.tcenv);
                              wl_implicits = (uu___1742_12518.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1742_12518.repr_subcomp_allowed)
                            } in
                          solve env uu____12517))))
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
            let uu____12558 = solve_universe_eq (p_pid orig) wl u1 u2 in
            match uu____12558 with
            | USolved wl1 ->
                let uu____12560 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1 in
                solve env uu____12560
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12563 = defer_lit "" orig wl1 in
                solve env uu____12563
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
                  let uu____12614 = solve_universe_eq (p_pid orig) wl1 u1 u2 in
                  (match uu____12614 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12617 -> ufailed_simple "Unequal number of universes" in
            let t11 = whnf env t1 in
            let t21 = whnf env t2 in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12630;
                  FStar_Syntax_Syntax.vars = uu____12631;_},
                us1),
               FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12634;
                  FStar_Syntax_Syntax.vars = uu____12635;_},
                us2)) ->
                let b = FStar_Syntax_Syntax.fv_eq f g in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12648, uu____12649) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12657, FStar_Syntax_Syntax.Tm_uinst uu____12658) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12666 -> USolved wl
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
            ((let uu____12677 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____12677
              then
                let uu____12682 = prob_to_string env orig in
                let uu____12684 = FStar_Thunk.force msg in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12682 uu____12684
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
            let uu___1824_12699 = wl1 in
            let uu____12700 =
              let uu____12710 =
                let uu____12718 = FStar_Thunk.mkv reason in
                ((wl1.ctr), uu____12718, orig) in
              uu____12710 :: (wl1.wl_deferred_to_tac) in
            {
              attempting = (uu___1824_12699.attempting);
              wl_deferred = (uu___1824_12699.wl_deferred);
              wl_deferred_to_tac = uu____12700;
              ctr = (uu___1824_12699.ctr);
              defer_ok = (uu___1824_12699.defer_ok);
              smt_ok = (uu___1824_12699.smt_ok);
              umax_heuristic_ok = (uu___1824_12699.umax_heuristic_ok);
              tcenv = (uu___1824_12699.tcenv);
              wl_implicits = (uu___1824_12699.wl_implicits);
              repr_subcomp_allowed = (uu___1824_12699.repr_subcomp_allowed)
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
                let uu____12747 = FStar_Syntax_Util.head_and_args t in
                match uu____12747 with
                | (head, uu____12771) ->
                    let uu____12796 =
                      let uu____12797 = FStar_Syntax_Subst.compress head in
                      uu____12797.FStar_Syntax_Syntax.n in
                    (match uu____12796 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv, uu____12807) ->
                         let uu____12824 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv in
                         (uu____12824,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12828 -> (false, "")) in
              let uu____12833 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs in
              (match uu____12833 with
               | (l1, r1) ->
                   let uu____12846 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs in
                   (match uu____12846 with
                    | (l2, r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12863 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl in
                           solve env uu____12863)))
          | uu____12864 ->
              let uu____12865 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl in
              solve env uu____12865
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
               let uu____12951 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements" in
               match uu____12951 with
               | (p, wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3)) in
             let pairwise t1 t2 wl2 =
               (let uu____13006 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel") in
                if uu____13006
                then
                  let uu____13011 = FStar_Syntax_Print.term_to_string t1 in
                  let uu____13013 = FStar_Syntax_Print.term_to_string t2 in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____13011 uu____13013
                else ());
               (let uu____13018 = head_matches_delta env1 wl2 t1 t2 in
                match uu____13018 with
                | (mr, ts1) ->
                    (match mr with
                     | HeadMatch (true) ->
                         let uu____13064 = eq_prob t1 t2 wl2 in
                         (match uu____13064 with | (p, wl3) -> (t1, [p], wl3))
                     | MisMatch uu____13085 ->
                         let uu____13094 = eq_prob t1 t2 wl2 in
                         (match uu____13094 with | (p, wl3) -> (t1, [p], wl3))
                     | FullMatch ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11, t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false) ->
                         let uu____13144 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11, t21) ->
                               let uu____13159 =
                                 FStar_Syntax_Subst.compress t11 in
                               let uu____13160 =
                                 FStar_Syntax_Subst.compress t21 in
                               (uu____13159, uu____13160)
                           | FStar_Pervasives_Native.None ->
                               let uu____13165 =
                                 FStar_Syntax_Subst.compress t1 in
                               let uu____13166 =
                                 FStar_Syntax_Subst.compress t2 in
                               (uu____13165, uu____13166) in
                         (match uu____13144 with
                          | (t11, t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13197 =
                                  FStar_Syntax_Util.head_and_args t12 in
                                match uu____13197 with
                                | (t1_hd, t1_args) ->
                                    let uu____13242 =
                                      FStar_Syntax_Util.head_and_args t22 in
                                    (match uu____13242 with
                                     | (t2_hd, t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13308 =
                                              let uu____13315 =
                                                let uu____13326 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd in
                                                uu____13326 :: t1_args in
                                              let uu____13343 =
                                                let uu____13352 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd in
                                                uu____13352 :: t2_args in
                                              FStar_List.fold_left2
                                                (fun uu____13401 ->
                                                   fun uu____13402 ->
                                                     fun uu____13403 ->
                                                       match (uu____13401,
                                                               uu____13402,
                                                               uu____13403)
                                                       with
                                                       | ((probs, wl4),
                                                          (a1, uu____13453),
                                                          (a2, uu____13455))
                                                           ->
                                                           let uu____13492 =
                                                             eq_prob a1 a2
                                                               wl4 in
                                                           (match uu____13492
                                                            with
                                                            | (p, wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13315
                                                uu____13343 in
                                            match uu____13308 with
                                            | (probs, wl4) ->
                                                let wl' =
                                                  let uu___1927_13518 = wl4 in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1927_13518.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1927_13518.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1927_13518.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1927_13518.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1927_13518.repr_subcomp_allowed)
                                                  } in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____13529 =
                                                  solve env1 wl' in
                                                (match uu____13529 with
                                                 | Success
                                                     (uu____13532,
                                                      defer_to_tac, imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13536 =
                                                         extend_wl wl4
                                                           defer_to_tac imps in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13536))
                                                 | Failed uu____13537 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None)))) in
                              let combine t12 t22 wl3 =
                                let uu____13569 =
                                  base_and_refinement_maybe_delta false env1
                                    t12 in
                                match uu____13569 with
                                | (t1_base, p1_opt) ->
                                    let uu____13605 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22 in
                                    (match uu____13605 with
                                     | (t2_base, p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13704 =
                                               FStar_Syntax_Util.is_t_true t in
                                             if uu____13704
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
                                               let uu____13757 =
                                                 op phi11 phi21 in
                                               refine x1 uu____13757
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
                                               let uu____13789 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____13789
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
                                               let uu____13821 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1 in
                                               refine x1 uu____13821
                                           | uu____13824 -> t_base in
                                         let uu____13841 =
                                           try_eq t1_base t2_base wl3 in
                                         (match uu____13841 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13855 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt in
                                              (uu____13855, [], wl4)
                                          | FStar_Pervasives_Native.None ->
                                              let uu____13862 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12 in
                                              (match uu____13862 with
                                               | (t1_base1, p1_opt1) ->
                                                   let uu____13898 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22 in
                                                   (match uu____13898 with
                                                    | (t2_base1, p2_opt1) ->
                                                        let uu____13934 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3 in
                                                        (match uu____13934
                                                         with
                                                         | (p, wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1 in
                                                             (t, [p], wl4)))))) in
                              let uu____13958 = combine t11 t21 wl2 in
                              (match uu____13958 with
                               | (t12, ps, wl3) ->
                                   ((let uu____13991 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel") in
                                     if uu____13991
                                     then
                                       let uu____13996 =
                                         FStar_Syntax_Print.term_to_string
                                           t12 in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13996
                                     else ());
                                    (t12, ps, wl3)))))) in
             let rec aux uu____14038 ts1 =
               match uu____14038 with
               | (out, probs, wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____14101 = pairwise out t wl2 in
                        (match uu____14101 with
                         | (out1, probs', wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2)) in
             let uu____14137 =
               let uu____14148 = FStar_List.hd ts in (uu____14148, [], wl1) in
             let uu____14157 = FStar_List.tl ts in
             aux uu____14137 uu____14157 in
           let uu____14164 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs)) in
           match uu____14164 with
           | (this_flex, this_rigid) ->
               let uu____14190 =
                 let uu____14191 = FStar_Syntax_Subst.compress this_rigid in
                 uu____14191.FStar_Syntax_Syntax.n in
               (match uu____14190 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs, comp) ->
                    let uu____14216 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp in
                    if uu____14216
                    then
                      let uu____14219 = destruct_flex_t this_flex wl in
                      (match uu____14219 with
                       | (flex, wl1) ->
                           let uu____14226 = quasi_pattern env flex in
                           (match uu____14226 with
                            | FStar_Pervasives_Native.None ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs, flex_t1)
                                ->
                                ((let uu____14245 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel") in
                                  if uu____14245
                                  then
                                    let uu____14250 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14250
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14257 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2037_14260 = tp in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2037_14260.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2037_14260.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2037_14260.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2037_14260.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2037_14260.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2037_14260.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2037_14260.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2037_14260.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2037_14260.FStar_TypeChecker_Common.rank)
                                }))] wl in
                       solve env uu____14257)
                | uu____14261 ->
                    ((let uu____14263 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel") in
                      if uu____14263
                      then
                        let uu____14268 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14268
                      else ());
                     (let uu____14273 =
                        FStar_Syntax_Util.head_and_args this_flex in
                      match uu____14273 with
                      | (u, _args) ->
                          let uu____14316 =
                            let uu____14317 = FStar_Syntax_Subst.compress u in
                            uu____14317.FStar_Syntax_Syntax.n in
                          (match uu____14316 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar, _subst)
                               ->
                               let equiv t =
                                 let uu____14345 =
                                   FStar_Syntax_Util.head_and_args t in
                                 match uu____14345 with
                                 | (u', uu____14364) ->
                                     let uu____14389 =
                                       let uu____14390 = whnf env u' in
                                       uu____14390.FStar_Syntax_Syntax.n in
                                     (match uu____14389 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar', _subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14412 -> false) in
                               let uu____14414 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_14437 ->
                                         match uu___23_14437 with
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
                                              | uu____14451 -> false)
                                         | uu____14455 -> false)) in
                               (match uu____14414 with
                                | (bounds_probs, rest) ->
                                    let bounds_typs =
                                      let uu____14470 = whnf env this_rigid in
                                      let uu____14471 =
                                        FStar_List.collect
                                          (fun uu___24_14477 ->
                                             match uu___24_14477 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14483 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs in
                                                 [uu____14483]
                                             | uu____14487 -> [])
                                          bounds_probs in
                                      uu____14470 :: uu____14471 in
                                    let uu____14488 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl in
                                    (match uu____14488 with
                                     | (bound, sub_probs, wl1) ->
                                         let uu____14521 =
                                           let flex_u =
                                             flex_uvar_head this_flex in
                                           let bound1 =
                                             let uu____14536 =
                                               let uu____14537 =
                                                 FStar_Syntax_Subst.compress
                                                   bound in
                                               uu____14537.FStar_Syntax_Syntax.n in
                                             match uu____14536 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x, phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14549 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14549)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14560 -> bound in
                                           let uu____14561 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements") in
                                           (bound1, uu____14561) in
                                         (match uu____14521 with
                                          | (bound_typ, (eq_prob, wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14596 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel") in
                                                if uu____14596
                                                then
                                                  let wl'1 =
                                                    let uu___2097_14602 = wl1 in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2097_14602.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2097_14602.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2097_14602.ctr);
                                                      defer_ok =
                                                        (uu___2097_14602.defer_ok);
                                                      smt_ok =
                                                        (uu___2097_14602.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2097_14602.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2097_14602.tcenv);
                                                      wl_implicits =
                                                        (uu___2097_14602.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2097_14602.repr_subcomp_allowed)
                                                    } in
                                                  let uu____14603 =
                                                    wl_to_string wl'1 in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14603
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    () in
                                                let uu____14609 =
                                                  solve_t env eq_prob
                                                    (let uu___2102_14611 =
                                                       wl' in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2102_14611.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2102_14611.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2102_14611.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2102_14611.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2102_14611.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2102_14611.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2102_14611.repr_subcomp_allowed)
                                                     }) in
                                                match uu____14609 with
                                                | Success
                                                    (uu____14613,
                                                     defer_to_tac, imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2109_14617 =
                                                        wl' in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2109_14617.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2109_14617.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2109_14617.ctr);
                                                        defer_ok =
                                                          (uu___2109_14617.defer_ok);
                                                        smt_ok =
                                                          (uu___2109_14617.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2109_14617.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2109_14617.tcenv);
                                                        wl_implicits =
                                                          (uu___2109_14617.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2109_14617.repr_subcomp_allowed)
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
                                                    let uu____14634 =
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
                                                    ((let uu____14646 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel") in
                                                      if uu____14646
                                                      then
                                                        let uu____14651 =
                                                          let uu____14653 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs) in
                                                          FStar_All.pipe_right
                                                            uu____14653
                                                            (FStar_String.concat
                                                               "\n") in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14651
                                                      else ());
                                                     (let uu____14666 =
                                                        let uu____14681 =
                                                          base_and_refinement
                                                            env bound_typ in
                                                        (rank1, uu____14681) in
                                                      match uu____14666 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          uu____14703)) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14729 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____14729
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
                                                                  let uu____14749
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____14749))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid,
                                                         (t_base,
                                                          FStar_Pervasives_Native.Some
                                                          (x, phi))) ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14774 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping" in
                                                            match uu____14774
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
                                                                    let uu____14794
                                                                    =
                                                                    let uu____14799
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1)) in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14799 in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14794
                                                                    [] wl2 in
                                                                  let uu____14805
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3 in
                                                                  solve env
                                                                    uu____14805))))
                                                      | uu____14806 ->
                                                          let uu____14821 =
                                                            FStar_Thunk.map
                                                              (fun s ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg in
                                                          giveup env
                                                            uu____14821 p)))))))
                           | uu____14828 when flip ->
                               let uu____14829 =
                                 let uu____14831 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____14833 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14831 uu____14833 in
                               failwith uu____14829
                           | uu____14836 ->
                               let uu____14837 =
                                 let uu____14839 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1) in
                                 let uu____14841 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp) in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14839 uu____14841 in
                               failwith uu____14837)))))
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
                      (fun uu____14877 ->
                         match uu____14877 with
                         | (x, i) ->
                             let uu____14896 =
                               FStar_Syntax_Syntax.bv_to_name x in
                             (uu____14896, i)) bs_lhs in
                  let uu____14899 = lhs in
                  match uu____14899 with
                  | Flex (uu____14900, u_lhs, uu____14902) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14999 =
                            match uopt with
                            | FStar_Pervasives_Native.None ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____15009 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos in
                                (uu____15009, univ) in
                          match uu____14999 with
                          | (k, univ) ->
                              let uu____15016 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2 in
                              (match uu____15016 with
                               | (uu____15033, u, wl3) ->
                                   let uu____15036 =
                                     f u (FStar_Pervasives_Native.Some univ) in
                                   (uu____15036, wl3)) in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t, uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____15062 =
                              let uu____15075 =
                                let uu____15086 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ in
                                uu____15086 ::
                                  (ct.FStar_Syntax_Syntax.effect_args) in
                              FStar_List.fold_right
                                (fun uu____15137 ->
                                   fun uu____15138 ->
                                     match (uu____15137, uu____15138) with
                                     | ((a, i), (out_args, wl2)) ->
                                         let uu____15239 =
                                           let uu____15246 =
                                             let uu____15249 =
                                               FStar_Syntax_Util.type_u () in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15249 in
                                           copy_uvar u_lhs [] uu____15246 wl2 in
                                         (match uu____15239 with
                                          | (uu____15278, t_a, wl3) ->
                                              let uu____15281 =
                                                copy_uvar u_lhs bs t_a wl3 in
                                              (match uu____15281 with
                                               | (uu____15300, a', wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____15075
                                ([], wl1) in
                            (match uu____15062 with
                             | (out_args, wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_15369 ->
                                        match uu___25_15369 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____15371 -> false
                                        | uu____15375 -> true) flags in
                                 let ct' =
                                   let uu___2228_15378 = ct in
                                   let uu____15379 =
                                     let uu____15382 = FStar_List.hd out_args in
                                     FStar_Pervasives_Native.fst uu____15382 in
                                   let uu____15397 = FStar_List.tl out_args in
                                   let uu____15414 =
                                     nodec ct.FStar_Syntax_Syntax.flags in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2228_15378.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2228_15378.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15379;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15397;
                                     FStar_Syntax_Syntax.flags = uu____15414
                                   } in
                                 ((let uu___2231_15418 = c in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2231_15418.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2231_15418.FStar_Syntax_Syntax.vars)
                                   }), wl2)) in
                      let uu____15421 =
                        FStar_Syntax_Util.arrow_formals_comp arrow in
                      (match uu____15421 with
                       | (formals, c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15459 =
                                   imitate_comp bs bs_terms c wl1 in
                                 (match uu____15459 with
                                  | (c', wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c' in
                                      let sol =
                                        let uu____15470 =
                                          let uu____15475 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____15475) in
                                        TERM uu____15470 in
                                      let uu____15476 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation" in
                                      (match uu____15476 with
                                       | (sub_prob, wl3) ->
                                           let uu____15490 =
                                             let uu____15491 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3 in
                                             attempt [sub_prob] uu____15491 in
                                           solve env uu____15490))
                             | (x, imp)::formals2 ->
                                 let uu____15513 =
                                   let uu____15520 =
                                     let uu____15523 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_right uu____15523
                                       FStar_Pervasives_Native.fst in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15520 wl1 in
                                 (match uu____15513 with
                                  | (_ctx_u_x, u_x, wl2) ->
                                      let y =
                                        let uu____15544 =
                                          let uu____15547 =
                                            FStar_Syntax_Syntax.range_of_bv x in
                                          FStar_Pervasives_Native.Some
                                            uu____15547 in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15544 u_x in
                                      let uu____15548 =
                                        let uu____15551 =
                                          let uu____15554 =
                                            let uu____15555 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y in
                                            (uu____15555, imp) in
                                          [uu____15554] in
                                        FStar_List.append bs_terms
                                          uu____15551 in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15548 formals2 wl2) in
                           let uu____15582 = occurs_check u_lhs arrow in
                           (match uu____15582 with
                            | (uu____15595, occurs_ok, msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15611 =
                                    mklstr
                                      (fun uu____15616 ->
                                         let uu____15617 =
                                           FStar_Option.get msg in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15617) in
                                  giveup_or_defer env orig wl uu____15611
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
              (let uu____15650 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____15650
               then
                 let uu____15655 =
                   FStar_Syntax_Print.binders_to_string ", " bs1 in
                 let uu____15658 =
                   FStar_Syntax_Print.binders_to_string ", " bs2 in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15655 (rel_to_string (p_rel orig)) uu____15658
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([], []) ->
                     let uu____15789 = rhs wl1 scope env1 subst in
                     (match uu____15789 with
                      | (rhs_prob, wl2) ->
                          ((let uu____15812 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel") in
                            if uu____15812
                            then
                              let uu____15817 = prob_to_string env1 rhs_prob in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15817
                            else ());
                           (let formula = p_guard rhs_prob in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1, imp)::xs1, (hd2, imp')::ys1) when
                     let uu____15895 = FStar_Syntax_Util.eq_aqual imp imp' in
                     uu____15895 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2301_15897 = hd1 in
                       let uu____15898 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2301_15897.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2301_15897.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15898
                       } in
                     let hd21 =
                       let uu___2304_15902 = hd2 in
                       let uu____15903 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2304_15902.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2304_15902.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15903
                       } in
                     let uu____15906 =
                       let uu____15911 =
                         FStar_All.pipe_left invert_rel (p_rel orig) in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15911
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter" in
                     (match uu____15906 with
                      | (prob, wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11 in
                          let subst1 =
                            let uu____15934 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15934 in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12 in
                          let uu____15941 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1 in
                          (match uu____15941 with
                           | (env3, FStar_Util.Inl (sub_probs, phi), wl3) ->
                               let phi1 =
                                 let uu____16013 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____16013 in
                               ((let uu____16031 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel") in
                                 if uu____16031
                                 then
                                   let uu____16036 =
                                     FStar_Syntax_Print.term_to_string phi1 in
                                   let uu____16038 =
                                     FStar_Syntax_Print.bv_to_string hd12 in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____16036
                                     uu____16038
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____16073 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1) in
               let uu____16109 = aux wl [] env [] bs1 bs2 in
               match uu____16109 with
               | (env1, FStar_Util.Inr msg, wl1) -> giveup_lit env1 msg orig
               | (env1, FStar_Util.Inl (sub_probs, phi), wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1 in
                   let uu____16168 = attempt sub_probs wl2 in
                   solve env1 uu____16168)
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
            let uu___2342_16188 = wl in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2342_16188.wl_deferred_to_tac);
              ctr = (uu___2342_16188.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2342_16188.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2342_16188.repr_subcomp_allowed)
            } in
          let tx = FStar_Syntax_Unionfind.new_transaction () in
          let uu____16200 = try_solve env wl' in
          match uu____16200 with
          | Success (uu____16201, defer_to_tac, imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps in solve env wl1))
          | Failed (p, s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))
and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16214 = compress_tprob wl.tcenv problem in
         solve_t' env uu____16214 wl)
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
            let uu____16220 = should_defer_flex_to_user_tac env wl lhs in
            if uu____16220
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16233 =
                   FStar_List.map FStar_Pervasives_Native.fst bs in
                 FStar_Util.as_set uu____16233 FStar_Syntax_Syntax.order_bv in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16267 = lhs1 in
                 match uu____16267 with
                 | Flex (uu____16270, ctx_u, uu____16272) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16280 ->
                           let uu____16281 = sn_binders env1 bs in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16281 rhs1 in
                     [TERM (ctx_u, sol)] in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16330 = quasi_pattern env1 lhs1 in
                 match uu____16330 with
                 | FStar_Pervasives_Native.None ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs, uu____16364) ->
                     let uu____16369 = lhs1 in
                     (match uu____16369 with
                      | Flex (t_lhs, ctx_u, args) ->
                          let uu____16384 = occurs_check ctx_u rhs1 in
                          (match uu____16384 with
                           | (uvars, occurs_ok, msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16435 =
                                   let uu____16443 =
                                     let uu____16445 = FStar_Option.get msg in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16445 in
                                   FStar_Util.Inl uu____16443 in
                                 (uu____16435, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs) in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1 in
                                  let uu____16473 =
                                    let uu____16475 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs in
                                    Prims.op_Negation uu____16475 in
                                  if uu____16473
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16502 =
                                       let uu____16510 =
                                         mk_solution env1 lhs1 bs rhs1 in
                                       FStar_Util.Inr uu____16510 in
                                     let uu____16516 =
                                       restrict_all_uvars ctx_u uvars [] wl1 in
                                     (uu____16502, uu____16516))))) in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16566 = FStar_Syntax_Util.head_and_args rhs1 in
                 match uu____16566 with
                 | (rhs_hd, args) ->
                     let uu____16609 = FStar_Util.prefix args in
                     (match uu____16609 with
                      | (args_rhs, last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              rhs1.FStar_Syntax_Syntax.pos in
                          let uu____16679 = lhs1 in
                          (match uu____16679 with
                           | Flex (t_lhs, u_lhs, _lhs_args) ->
                               let uu____16683 =
                                 let uu____16694 =
                                   let uu____16701 =
                                     let uu____16704 =
                                       FStar_Syntax_Util.type_u () in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16704 in
                                   copy_uvar u_lhs [] uu____16701 wl1 in
                                 match uu____16694 with
                                 | (uu____16731, t_last_arg, wl2) ->
                                     let uu____16734 =
                                       let uu____16741 =
                                         let uu____16742 =
                                           let uu____16751 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg in
                                           [uu____16751] in
                                         FStar_List.append bs_lhs uu____16742 in
                                       copy_uvar u_lhs uu____16741 t_res_lhs
                                         wl2 in
                                     (match uu____16734 with
                                      | (uu____16786, lhs', wl3) ->
                                          let uu____16789 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3 in
                                          (match uu____16789 with
                                           | (uu____16806, lhs'_last_arg,
                                              wl4) ->
                                               (lhs', lhs'_last_arg, wl4))) in
                               (match uu____16683 with
                                | (lhs', lhs'_last_arg, wl2) ->
                                    let sol =
                                      let uu____16827 =
                                        let uu____16828 =
                                          let uu____16833 =
                                            let uu____16834 =
                                              let uu____16837 =
                                                let uu____16838 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    lhs'_last_arg in
                                                [uu____16838] in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                lhs' uu____16837
                                                t_lhs.FStar_Syntax_Syntax.pos in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16834
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs)) in
                                          (u_lhs, uu____16833) in
                                        TERM uu____16828 in
                                      [uu____16827] in
                                    let uu____16863 =
                                      let uu____16870 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs" in
                                      match uu____16870 with
                                      | (p1, wl3) ->
                                          let uu____16890 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs" in
                                          (match uu____16890 with
                                           | (p2, wl4) -> ([p1; p2], wl4)) in
                                    (match uu____16863 with
                                     | (sub_probs, wl3) ->
                                         let uu____16922 =
                                           let uu____16923 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3 in
                                           attempt sub_probs uu____16923 in
                                         solve env1 uu____16922)))) in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16957 = FStar_Syntax_Util.head_and_args rhs2 in
                   match uu____16957 with
                   | (uu____16975, args) ->
                       (match args with | [] -> false | uu____17011 -> true) in
                 let is_arrow rhs2 =
                   let uu____17030 =
                     let uu____17031 = FStar_Syntax_Subst.compress rhs2 in
                     uu____17031.FStar_Syntax_Syntax.n in
                   match uu____17030 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____17035 -> true
                   | uu____17051 -> false in
                 let uu____17053 = quasi_pattern env1 lhs1 in
                 match uu____17053 with
                 | FStar_Pervasives_Native.None ->
                     let msg =
                       mklstr
                         (fun uu____17072 ->
                            let uu____17073 = prob_to_string env1 orig1 in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____17073) in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs, t_res_lhs) ->
                     let uu____17082 = is_app rhs1 in
                     if uu____17082
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____17087 = is_arrow rhs1 in
                        if uu____17087
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu____17100 ->
                                  let uu____17101 = prob_to_string env1 orig1 in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____17101) in
                           giveup_or_defer env1 orig1 wl1 msg)) in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB ->
                   if wl.defer_ok
                   then
                     let uu____17105 = FStar_Thunk.mkv "flex-rigid subtyping" in
                     giveup_or_defer env orig wl uu____17105
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV ->
                   if wl.defer_ok
                   then
                     let uu____17111 = FStar_Thunk.mkv "flex-rigid subtyping" in
                     giveup_or_defer env orig wl uu____17111
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ ->
                   let uu____17116 = lhs in
                   (match uu____17116 with
                    | Flex (_t1, ctx_uv, args_lhs) ->
                        let uu____17120 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs in
                        (match uu____17120 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs in
                             let names_to_string1 fvs =
                               let uu____17138 =
                                 let uu____17142 =
                                   FStar_Util.set_elements fvs in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____17142 in
                               FStar_All.pipe_right uu____17138
                                 (FStar_String.concat ", ") in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders) in
                             let fvs2 = FStar_Syntax_Free.names rhs1 in
                             let uu____17163 = occurs_check ctx_uv rhs1 in
                             (match uu____17163 with
                              | (uvars, occurs_ok, msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17192 =
                                      let uu____17193 =
                                        let uu____17195 =
                                          FStar_Option.get msg in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17195 in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17193 in
                                    giveup_or_defer env orig wl uu____17192
                                  else
                                    (let uu____17203 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1 in
                                     if uu____17203
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1 in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars
                                           lhs_binders wl in
                                       let uu____17210 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1 in
                                       solve env uu____17210
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            mklstr
                                              (fun uu____17226 ->
                                                 let uu____17227 =
                                                   names_to_string1 fvs2 in
                                                 let uu____17229 =
                                                   names_to_string1 fvs1 in
                                                 let uu____17231 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders) in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17227 uu____17229
                                                   uu____17231) in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17243 ->
                             if wl.defer_ok
                             then
                               let uu____17247 =
                                 FStar_Thunk.mkv "Not a pattern" in
                               giveup_or_defer env orig wl uu____17247
                             else
                               (let uu____17252 =
                                  try_quasi_pattern orig env wl lhs rhs in
                                match uu____17252 with
                                | (FStar_Util.Inr sol, wl1) ->
                                    let uu____17278 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1 in
                                    solve env uu____17278
                                | (FStar_Util.Inl msg, uu____17280) ->
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
                  let uu____17298 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____17298
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV ->
                if wl.defer_ok
                then
                  let uu____17304 = FStar_Thunk.mkv "flex-flex subtyping" in
                  giveup_or_defer env orig wl uu____17304
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ ->
                let uu____17309 =
                  (should_defer_flex_to_user_tac env wl lhs) ||
                    (should_defer_flex_to_user_tac env wl rhs) in
                if uu____17309
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
                    (let uu____17316 =
                       FStar_Thunk.mkv "flex-flex non-pattern" in
                     giveup_or_defer env orig wl uu____17316)
                  else
                    (let uu____17321 =
                       let uu____17338 = quasi_pattern env lhs in
                       let uu____17345 = quasi_pattern env rhs in
                       (uu____17338, uu____17345) in
                     match uu____17321 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs, t_res_lhs),
                        FStar_Pervasives_Native.Some
                        (binders_rhs, t_res_rhs)) ->
                         let uu____17388 = lhs in
                         (match uu____17388 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17389;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17391;_},
                               u_lhs, uu____17393)
                              ->
                              let uu____17396 = rhs in
                              (match uu____17396 with
                               | Flex (uu____17397, u_rhs, uu____17399) ->
                                   let uu____17400 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs) in
                                   if uu____17400
                                   then
                                     let uu____17407 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl in
                                     solve env uu____17407
                                   else
                                     (let uu____17410 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders in
                                      match uu____17410 with
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
                                          let uu____17442 =
                                            let uu____17449 =
                                              let uu____17452 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17452 in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____17449
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None in
                                          (match uu____17442 with
                                           | (uu____17458, w, wl1) ->
                                               let w_app =
                                                 let uu____17462 =
                                                   FStar_List.map
                                                     (fun uu____17473 ->
                                                        match uu____17473
                                                        with
                                                        | (z, uu____17481) ->
                                                            let uu____17486 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____17486) zs in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____17462
                                                   w.FStar_Syntax_Syntax.pos in
                                               ((let uu____17488 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____17488
                                                 then
                                                   let uu____17493 =
                                                     let uu____17497 =
                                                       flex_t_to_string lhs in
                                                     let uu____17499 =
                                                       let uu____17503 =
                                                         flex_t_to_string rhs in
                                                       let uu____17505 =
                                                         let uu____17509 =
                                                           term_to_string w in
                                                         let uu____17511 =
                                                           let uu____17515 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs) in
                                                           let uu____17524 =
                                                             let uu____17528
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs) in
                                                             let uu____17537
                                                               =
                                                               let uu____17541
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs in
                                                               [uu____17541] in
                                                             uu____17528 ::
                                                               uu____17537 in
                                                           uu____17515 ::
                                                             uu____17524 in
                                                         uu____17509 ::
                                                           uu____17511 in
                                                       uu____17503 ::
                                                         uu____17505 in
                                                     uu____17497 ::
                                                       uu____17499 in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17493
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17558 =
                                                       let uu____17563 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs)) in
                                                       (u_lhs, uu____17563) in
                                                     TERM uu____17558 in
                                                   let uu____17564 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   if uu____17564
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17572 =
                                                          let uu____17577 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs)) in
                                                          (u_rhs,
                                                            uu____17577) in
                                                        TERM uu____17572 in
                                                      [s1; s2]) in
                                                 let uu____17578 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1 in
                                                 solve env uu____17578))))))
                     | uu____17579 ->
                         let uu____17596 =
                           FStar_Thunk.mkv "flex-flex: non-patterns" in
                         giveup_or_defer env orig wl uu____17596)
and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env ->
    fun problem ->
      fun wl ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____17650 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel") in
            if uu____17650
            then
              let uu____17655 = FStar_Syntax_Print.term_to_string t1 in
              let uu____17657 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____17659 = FStar_Syntax_Print.term_to_string t2 in
              let uu____17661 = FStar_Syntax_Print.tag_of_term t2 in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17655 uu____17657 uu____17659 uu____17661
            else ());
           (let uu____17672 = FStar_Syntax_Util.head_and_args t1 in
            match uu____17672 with
            | (head1, args1) ->
                let uu____17715 = FStar_Syntax_Util.head_and_args t2 in
                (match uu____17715 with
                 | (head2, args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17785 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2 in
                          match uu____17785 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17790 =
                                defer_lit "universe constraints" orig wl3 in
                              k false uu____17790) in
                     let nargs = FStar_List.length args1 in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17811 =
                         mklstr
                           (fun uu____17822 ->
                              let uu____17823 =
                                FStar_Syntax_Print.term_to_string head1 in
                              let uu____17825 = args_to_string args1 in
                              let uu____17829 =
                                FStar_Syntax_Print.term_to_string head2 in
                              let uu____17831 = args_to_string args2 in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17823 uu____17825 uu____17829
                                uu____17831) in
                       giveup env1 uu____17811 orig
                     else
                       (let uu____17838 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17843 =
                               FStar_Syntax_Util.eq_args args1 args2 in
                             uu____17843 = FStar_Syntax_Util.Equal) in
                        if uu____17838
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2614_17847 = problem in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2614_17847.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2614_17847.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2614_17847.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2614_17847.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2614_17847.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2614_17847.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2614_17847.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2614_17847.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok ->
                                  fun wl2 ->
                                    if ok
                                    then
                                      let uu____17857 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2 in
                                      solve env1 uu____17857
                                    else solve env1 wl2))
                        else
                          (let uu____17862 = base_and_refinement env1 t1 in
                           match uu____17862 with
                           | (base1, refinement1) ->
                               let uu____17887 = base_and_refinement env1 t2 in
                               (match uu____17887 with
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
                                           let uu____18052 =
                                             FStar_List.fold_right
                                               (fun uu____18092 ->
                                                  fun uu____18093 ->
                                                    match (uu____18092,
                                                            uu____18093)
                                                    with
                                                    | (((a1, uu____18145),
                                                        (a2, uu____18147)),
                                                       (probs, wl3)) ->
                                                        let uu____18196 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index" in
                                                        (match uu____18196
                                                         with
                                                         | (prob', wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2) in
                                           match uu____18052 with
                                           | (subprobs, wl3) ->
                                               ((let uu____18239 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____18239
                                                 then
                                                   let uu____18244 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18244
                                                 else ());
                                                (let uu____18250 =
                                                   FStar_Options.defensive () in
                                                 if uu____18250
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
                                                    (let uu____18277 =
                                                       mk_sub_probs wl3 in
                                                     match uu____18277 with
                                                     | (subprobs, wl4) ->
                                                         let formula =
                                                           let uu____18293 =
                                                             FStar_List.map
                                                               (fun p ->
                                                                  p_guard p)
                                                               subprobs in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18293 in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4 in
                                                         let uu____18301 =
                                                           attempt subprobs
                                                             wl5 in
                                                         solve env2
                                                           uu____18301)) in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok ->
                                                fun wl3 ->
                                                  let uu____18326 =
                                                    mk_sub_probs wl3 in
                                                  match uu____18326 with
                                                  | (subprobs, wl4) ->
                                                      let formula =
                                                        let uu____18342 =
                                                          FStar_List.map
                                                            (fun p ->
                                                               p_guard p)
                                                            subprobs in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18342 in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4 in
                                                      let uu____18350 =
                                                        attempt subprobs wl5 in
                                                      solve env2 uu____18350) in
                                         let unfold_and_retry d env2 wl2
                                           uu____18378 =
                                           match uu____18378 with
                                           | (prob, reason) ->
                                               ((let uu____18395 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel") in
                                                 if uu____18395
                                                 then
                                                   let uu____18400 =
                                                     prob_to_string env2 orig in
                                                   let uu____18402 =
                                                     FStar_Thunk.force reason in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____18400 uu____18402
                                                 else ());
                                                (let uu____18408 =
                                                   let uu____18417 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1 in
                                                   let uu____18420 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2 in
                                                   (uu____18417, uu____18420) in
                                                 match uu____18408 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',
                                                    FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18433 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1' in
                                                     (match uu____18433 with
                                                      | (head1', uu____18451)
                                                          ->
                                                          let uu____18476 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2' in
                                                          (match uu____18476
                                                           with
                                                           | (head2',
                                                              uu____18494) ->
                                                               let uu____18519
                                                                 =
                                                                 let uu____18524
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1 in
                                                                 let uu____18525
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2 in
                                                                 (uu____18524,
                                                                   uu____18525) in
                                                               (match uu____18519
                                                                with
                                                                | (FStar_Syntax_Util.Equal,
                                                                   FStar_Syntax_Util.Equal)
                                                                    ->
                                                                    (
                                                                    (
                                                                    let uu____18527
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____18527
                                                                    then
                                                                    let uu____18532
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1 in
                                                                    let uu____18534
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1' in
                                                                    let uu____18536
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2 in
                                                                    let uu____18538
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2' in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18532
                                                                    uu____18534
                                                                    uu____18536
                                                                    uu____18538
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18543
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2702_18551
                                                                    = torig in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2702_18551.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2702_18551.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2702_18551.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2702_18551.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2702_18551.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2702_18551.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2702_18551.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2702_18551.FStar_TypeChecker_Common.rank)
                                                                    } in
                                                                    ((
                                                                    let uu____18553
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel") in
                                                                    if
                                                                    uu____18553
                                                                    then
                                                                    let uu____18558
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig') in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18558
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18563 ->
                                                     solve_sub_probs env2 wl2)) in
                                         let d =
                                           let uu____18575 =
                                             delta_depth_of_term env1 head1 in
                                           match uu____18575 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d in
                                         let treat_as_injective =
                                           let uu____18583 =
                                             let uu____18584 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1 in
                                             uu____18584.FStar_Syntax_Syntax.n in
                                           match uu____18583 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18589 -> false in
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
                                          | uu____18592 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18595 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1) in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2) in
                                         solve_t env1
                                           (let uu___2722_18631 = problem in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2722_18631.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2722_18631.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2722_18631.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2722_18631.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2722_18631.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2722_18631.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2722_18631.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2722_18631.FStar_TypeChecker_Common.rank)
                                            }) wl1)))))) in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18707 = destruct_flex_t scrutinee wl1 in
             match uu____18707 with
             | (Flex (_t, uv, _args), wl2) ->
                 let uu____18718 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p in
                 (match uu____18718 with
                  | (xs, pat_term, uu____18734, uu____18735) ->
                      let uu____18740 =
                        FStar_List.fold_left
                          (fun uu____18763 ->
                             fun x ->
                               match uu____18763 with
                               | (subst, wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort in
                                   let uu____18784 = copy_uvar uv [] t_x wl3 in
                                   (match uu____18784 with
                                    | (uu____18803, u, wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst in
                                        (subst1, wl4))) ([], wl2) xs in
                      (match uu____18740 with
                       | (subst, wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term in
                           let uu____18824 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic" in
                           (match uu____18824 with
                            | (prob, wl4) ->
                                let wl' =
                                  let uu___2763_18841 = wl4 in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2763_18841.wl_deferred_to_tac);
                                    ctr = (uu___2763_18841.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2763_18841.umax_heuristic_ok);
                                    tcenv = (uu___2763_18841.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2763_18841.repr_subcomp_allowed)
                                  } in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction () in
                                let uu____18852 = solve env1 wl' in
                                (match uu____18852 with
                                 | Success (uu____18855, defer_to_tac, imps)
                                     ->
                                     let wl'1 =
                                       let uu___2772_18859 = wl' in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2772_18859.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2772_18859.wl_deferred_to_tac);
                                         ctr = (uu___2772_18859.ctr);
                                         defer_ok =
                                           (uu___2772_18859.defer_ok);
                                         smt_ok = (uu___2772_18859.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2772_18859.umax_heuristic_ok);
                                         tcenv = (uu___2772_18859.tcenv);
                                         wl_implicits =
                                           (uu___2772_18859.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2772_18859.repr_subcomp_allowed)
                                       } in
                                     let uu____18860 = solve env1 wl'1 in
                                     (match uu____18860 with
                                      | Success
                                          (uu____18863, defer_to_tac', imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18867 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps') in
                                            FStar_Pervasives_Native.Some
                                              uu____18867))
                                      | Failed uu____18873 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18879 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None))))) in
           match t1t2_opt with
           | FStar_Pervasives_Native.None ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1, t2) ->
               ((let uu____18902 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel") in
                 if uu____18902
                 then
                   let uu____18907 = FStar_Syntax_Print.term_to_string t1 in
                   let uu____18909 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18907 uu____18909
                 else ());
                (let uu____18914 =
                   let uu____18935 =
                     let uu____18944 = FStar_Syntax_Util.unmeta t1 in
                     (s1, uu____18944) in
                   let uu____18951 =
                     let uu____18960 = FStar_Syntax_Util.unmeta t2 in
                     (s2, uu____18960) in
                   (uu____18935, uu____18951) in
                 match uu____18914 with
                 | ((uu____18990,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____18993;
                       FStar_Syntax_Syntax.vars = uu____18994;_}),
                    (s, t)) ->
                     let uu____19065 =
                       let uu____19067 = is_flex scrutinee in
                       Prims.op_Negation uu____19067 in
                     if uu____19065
                     then
                       ((let uu____19078 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____19078
                         then
                           let uu____19083 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19083
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19102 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19102
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19117 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19117
                           then
                             let uu____19122 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____19124 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19122 uu____19124
                           else ());
                          (let pat_discriminates uu___26_19149 =
                             match uu___26_19149 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19165;
                                  FStar_Syntax_Syntax.p = uu____19166;_},
                                FStar_Pervasives_Native.None, uu____19167) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19181;
                                  FStar_Syntax_Syntax.p = uu____19182;_},
                                FStar_Pervasives_Native.None, uu____19183) ->
                                 true
                             | uu____19210 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____19313 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____19313 with
                                       | (uu____19315, uu____19316, t') ->
                                           let uu____19334 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____19334 with
                                            | (FullMatch, uu____19346) ->
                                                true
                                            | (HeadMatch uu____19360,
                                               uu____19361) -> true
                                            | uu____19376 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____19413 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____19413
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19424 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____19424 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____19512, uu____19513)
                                       -> branches1
                                   | uu____19658 -> branches in
                                 let uu____19713 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____19722 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____19722 with
                                        | (p, uu____19726, uu____19727) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____19756 ->
                                      FStar_Util.Inr uu____19756) uu____19713))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19786 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____19786 with
                                | (p, uu____19795, e) ->
                                    ((let uu____19814 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____19814
                                      then
                                        let uu____19819 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____19821 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19819 uu____19821
                                      else ());
                                     (let uu____19826 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____19841 ->
                                           FStar_Util.Inr uu____19841)
                                        uu____19826)))))
                 | ((s, t),
                    (uu____19844,
                     {
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_match
                         (scrutinee, branches);
                       FStar_Syntax_Syntax.pos = uu____19847;
                       FStar_Syntax_Syntax.vars = uu____19848;_}))
                     ->
                     let uu____19917 =
                       let uu____19919 = is_flex scrutinee in
                       Prims.op_Negation uu____19919 in
                     if uu____19917
                     then
                       ((let uu____19930 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel") in
                         if uu____19930
                         then
                           let uu____19935 =
                             FStar_Syntax_Print.term_to_string scrutinee in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19935
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19954 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19954
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19969 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel") in
                           if uu____19969
                           then
                             let uu____19974 =
                               FStar_Syntax_Print.term_to_string scrutinee in
                             let uu____19976 =
                               FStar_Syntax_Print.term_to_string t in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19974 uu____19976
                           else ());
                          (let pat_discriminates uu___26_20001 =
                             match uu___26_20001 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____20017;
                                  FStar_Syntax_Syntax.p = uu____20018;_},
                                FStar_Pervasives_Native.None, uu____20019) ->
                                 true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____20033;
                                  FStar_Syntax_Syntax.p = uu____20034;_},
                                FStar_Pervasives_Native.None, uu____20035) ->
                                 true
                             | uu____20062 -> false in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b ->
                                     if pat_discriminates b
                                     then
                                       let uu____20165 =
                                         FStar_Syntax_Subst.open_branch b in
                                       match uu____20165 with
                                       | (uu____20167, uu____20168, t') ->
                                           let uu____20186 =
                                             head_matches_delta env1 wl1 s t' in
                                           (match uu____20186 with
                                            | (FullMatch, uu____20198) ->
                                                true
                                            | (HeadMatch uu____20212,
                                               uu____20213) -> true
                                            | uu____20228 -> false)
                                     else false)) in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None ->
                               ((let uu____20265 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel") in
                                 if uu____20265
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20276 =
                                     FStar_Util.prefix_until
                                       (fun b ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches in
                                   match uu____20276 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1, uu____20364, uu____20365)
                                       -> branches1
                                   | uu____20510 -> branches in
                                 let uu____20565 =
                                   FStar_Util.find_map try_branches
                                     (fun b ->
                                        let uu____20574 =
                                          FStar_Syntax_Subst.open_branch b in
                                        match uu____20574 with
                                        | (p, uu____20578, uu____20579) ->
                                            try_solve_branch scrutinee p) in
                                 FStar_All.pipe_left
                                   (fun uu____20608 ->
                                      FStar_Util.Inr uu____20608) uu____20565))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20638 =
                                 FStar_Syntax_Subst.open_branch b in
                               (match uu____20638 with
                                | (p, uu____20647, e) ->
                                    ((let uu____20666 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel") in
                                      if uu____20666
                                      then
                                        let uu____20671 =
                                          FStar_Syntax_Print.pat_to_string p in
                                        let uu____20673 =
                                          FStar_Syntax_Print.term_to_string e in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20671 uu____20673
                                      else ());
                                     (let uu____20678 =
                                        try_solve_branch scrutinee p in
                                      FStar_All.pipe_left
                                        (fun uu____20693 ->
                                           FStar_Util.Inr uu____20693)
                                        uu____20678)))))
                 | uu____20694 ->
                     ((let uu____20716 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel") in
                       if uu____20716
                       then
                         let uu____20721 = FStar_Syntax_Print.tag_of_term t1 in
                         let uu____20723 = FStar_Syntax_Print.tag_of_term t2 in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20721 uu____20723
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None))) in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig in
           (let uu____20769 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta") in
            if uu____20769
            then
              let uu____20774 = FStar_Syntax_Print.tag_of_term t1 in
              let uu____20776 = FStar_Syntax_Print.tag_of_term t2 in
              let uu____20778 = FStar_Syntax_Print.term_to_string t1 in
              let uu____20780 = FStar_Syntax_Print.term_to_string t2 in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20774 uu____20776 uu____20778 uu____20780
            else ());
           (let uu____20785 = head_matches_delta env1 wl1 t1 t2 in
            match uu____20785 with
            | (m, o) ->
                (match (m, o) with
                 | (MisMatch uu____20816, uu____20817) ->
                     let rec may_relate head =
                       let uu____20845 =
                         let uu____20846 = FStar_Syntax_Subst.compress head in
                         uu____20846.FStar_Syntax_Syntax.n in
                       match uu____20845 with
                       | FStar_Syntax_Syntax.Tm_name uu____20850 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20852 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20877 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv in
                           (match uu____20877 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20879 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20882
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20883 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t, uu____20886, uu____20887) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t, uu____20929) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t, uu____20935) ->
                           may_relate t
                       | uu____20940 -> false in
                     let uu____20942 =
                       try_match_heuristic env1 orig wl1 t1 t2 o in
                     (match uu____20942 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20955 =
                            FStar_Thunk.mkv "delaying match heuristic" in
                          giveup_or_defer1 orig uu____20955
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None) ->
                          let uu____20965 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok in
                          if uu____20965
                          then
                            let uu____20968 =
                              guard_of_prob env1 wl1 problem t1 t2 in
                            (match uu____20968 with
                             | (guard, wl2) ->
                                 let uu____20975 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2 in
                                 solve env1 uu____20975)
                          else
                            (let uu____20978 =
                               mklstr
                                 (fun uu____20989 ->
                                    let uu____20990 =
                                      FStar_Syntax_Print.term_to_string head1 in
                                    let uu____20992 =
                                      let uu____20994 =
                                        let uu____20998 =
                                          delta_depth_of_term env1 head1 in
                                        FStar_Util.bind_opt uu____20998
                                          (fun x ->
                                             let uu____21005 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____21005) in
                                      FStar_Util.dflt "" uu____20994 in
                                    let uu____21010 =
                                      FStar_Syntax_Print.term_to_string head2 in
                                    let uu____21012 =
                                      let uu____21014 =
                                        let uu____21018 =
                                          delta_depth_of_term env1 head2 in
                                        FStar_Util.bind_opt uu____21018
                                          (fun x ->
                                             let uu____21025 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x in
                                             FStar_Pervasives_Native.Some
                                               uu____21025) in
                                      FStar_Util.dflt "" uu____21014 in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20990 uu____20992 uu____21010
                                      uu____21012) in
                             giveup env1 uu____20978 orig))
                 | (HeadMatch (true), uu____21031) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____21046 = guard_of_prob env1 wl1 problem t1 t2 in
                       (match uu____21046 with
                        | (guard, wl2) ->
                            let uu____21053 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2 in
                            solve env1 uu____21053)
                     else
                       (let uu____21056 =
                          mklstr
                            (fun uu____21063 ->
                               let uu____21064 =
                                 FStar_Syntax_Print.term_to_string t1 in
                               let uu____21066 =
                                 FStar_Syntax_Print.term_to_string t2 in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____21064 uu____21066) in
                        giveup env1 uu____21056 orig)
                 | (uu____21069, FStar_Pervasives_Native.Some (t11, t21)) ->
                     solve_t env1
                       (let uu___2954_21083 = problem in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2954_21083.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2954_21083.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2954_21083.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2954_21083.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2954_21083.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2954_21083.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2954_21083.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2954_21083.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch, FStar_Pervasives_Native.None) ->
                     rigid_heads_match env1 false torig wl1 t1 t2)) in
         let orig = FStar_TypeChecker_Common.TProb problem in
         def_check_prob "solve_t'.2" orig;
         (let uu____21110 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs in
          if uu____21110
          then
            let uu____21113 =
              solve_prob orig FStar_Pervasives_Native.None [] wl in
            solve env uu____21113
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs in
             let t2 = problem.FStar_TypeChecker_Common.rhs in
             (let uu____21119 =
                let uu____21122 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____21122 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____21119 t1);
             (let uu____21141 =
                let uu____21144 = p_scope orig in
                FStar_List.map FStar_Pervasives_Native.fst uu____21144 in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____21141 t2);
             (let uu____21163 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel") in
              if uu____21163
              then
                let uu____21167 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid in
                let uu____21169 =
                  let uu____21171 = FStar_Syntax_Print.tag_of_term t1 in
                  let uu____21173 =
                    let uu____21175 = FStar_Syntax_Print.term_to_string t1 in
                    Prims.op_Hat "::" uu____21175 in
                  Prims.op_Hat uu____21171 uu____21173 in
                let uu____21178 =
                  let uu____21180 = FStar_Syntax_Print.tag_of_term t2 in
                  let uu____21182 =
                    let uu____21184 = FStar_Syntax_Print.term_to_string t2 in
                    Prims.op_Hat "::" uu____21184 in
                  Prims.op_Hat uu____21180 uu____21182 in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21167 uu____21169 uu____21178
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21191, uu____21192) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21208, FStar_Syntax_Syntax.Tm_delayed uu____21209) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21225, uu____21226) ->
                  let uu____21253 =
                    let uu___2985_21254 = problem in
                    let uu____21255 = FStar_Syntax_Util.unascribe t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2985_21254.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21255;
                      FStar_TypeChecker_Common.relation =
                        (uu___2985_21254.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2985_21254.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2985_21254.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2985_21254.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2985_21254.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2985_21254.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2985_21254.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2985_21254.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21253 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21256, uu____21257) ->
                  let uu____21264 =
                    let uu___2991_21265 = problem in
                    let uu____21266 = FStar_Syntax_Util.unmeta t1 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2991_21265.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21266;
                      FStar_TypeChecker_Common.relation =
                        (uu___2991_21265.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2991_21265.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2991_21265.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2991_21265.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2991_21265.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2991_21265.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2991_21265.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2991_21265.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21264 wl
              | (uu____21267, FStar_Syntax_Syntax.Tm_ascribed uu____21268) ->
                  let uu____21295 =
                    let uu___2997_21296 = problem in
                    let uu____21297 = FStar_Syntax_Util.unascribe t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2997_21296.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2997_21296.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2997_21296.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21297;
                      FStar_TypeChecker_Common.element =
                        (uu___2997_21296.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2997_21296.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2997_21296.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2997_21296.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2997_21296.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2997_21296.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21295 wl
              | (uu____21298, FStar_Syntax_Syntax.Tm_meta uu____21299) ->
                  let uu____21306 =
                    let uu___3003_21307 = problem in
                    let uu____21308 = FStar_Syntax_Util.unmeta t2 in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___3003_21307.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___3003_21307.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___3003_21307.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21308;
                      FStar_TypeChecker_Common.element =
                        (uu___3003_21307.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___3003_21307.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___3003_21307.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___3003_21307.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___3003_21307.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___3003_21307.FStar_TypeChecker_Common.rank)
                    } in
                  solve_t' env uu____21306 wl
              | (FStar_Syntax_Syntax.Tm_quoted (t11, uu____21310),
                 FStar_Syntax_Syntax.Tm_quoted (t21, uu____21312)) ->
                  let uu____21321 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl in
                  solve env uu____21321
              | (FStar_Syntax_Syntax.Tm_bvar uu____21322, uu____21323) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21325, FStar_Syntax_Syntax.Tm_bvar uu____21326) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1, FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow (bs1, c1),
                 FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) ->
                  let mk_c c uu___27_21396 =
                    match uu___27_21396 with
                    | [] -> c
                    | bs ->
                        let uu____21424 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos in
                        FStar_Syntax_Syntax.mk_Total uu____21424 in
                  let uu____21435 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)) in
                  (match uu____21435 with
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
                                    let uu____21584 =
                                      FStar_Options.use_eq_at_higher_order () in
                                    if uu____21584
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, lopt1),
                 FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, lopt2)) ->
                  let mk_t t l uu___28_21673 =
                    match uu___28_21673 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos in
                  let uu____21715 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2)) in
                  (match uu____21715 with
                   | ((bs11, tbody11), (bs21, tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1 ->
                            fun scope ->
                              fun env1 ->
                                fun subst ->
                                  let uu____21860 =
                                    FStar_Syntax_Subst.subst subst tbody11 in
                                  let uu____21861 =
                                    FStar_Syntax_Subst.subst subst tbody21 in
                                  mk_t_problem wl1 scope orig uu____21860
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21861 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21863, uu____21864) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21895 -> true
                    | uu____21915 -> false in
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
                      (let uu____21975 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3105_21983 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3105_21983.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3105_21983.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3105_21983.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3105_21983.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3105_21983.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3105_21983.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3105_21983.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3105_21983.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3105_21983.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3105_21983.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3105_21983.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3105_21983.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3105_21983.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3105_21983.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3105_21983.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3105_21983.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3105_21983.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3105_21983.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3105_21983.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3105_21983.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3105_21983.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3105_21983.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3105_21983.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3105_21983.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3105_21983.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3105_21983.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3105_21983.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3105_21983.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3105_21983.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3105_21983.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3105_21983.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3105_21983.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3105_21983.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3105_21983.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3105_21983.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3105_21983.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3105_21983.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3105_21983.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3105_21983.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3105_21983.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3105_21983.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3105_21983.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3105_21983.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3105_21983.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____21975 with
                       | (uu____21988, ty, uu____21990) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____21999 =
                                 let uu____22000 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____22000.FStar_Syntax_Syntax.n in
                               match uu____21999 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22003 ->
                                   let uu____22010 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____22010
                               | uu____22011 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____22014 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____22014
                             then
                               let uu____22019 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____22021 =
                                 let uu____22023 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22023 in
                               let uu____22024 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22019 uu____22021 uu____22024
                             else ());
                            r1)) in
                  let uu____22029 =
                    let uu____22046 = maybe_eta t1 in
                    let uu____22053 = maybe_eta t2 in
                    (uu____22046, uu____22053) in
                  (match uu____22029 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3126_22095 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3126_22095.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3126_22095.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3126_22095.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3126_22095.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3126_22095.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3126_22095.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3126_22095.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3126_22095.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____22116 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22116
                       then
                         let uu____22119 = destruct_flex_t not_abs wl in
                         (match uu____22119 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3143_22136 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3143_22136.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3143_22136.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3143_22136.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3143_22136.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3143_22136.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3143_22136.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3143_22136.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3143_22136.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22139 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22139 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____22162 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22162
                       then
                         let uu____22165 = destruct_flex_t not_abs wl in
                         (match uu____22165 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3143_22182 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3143_22182.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3143_22182.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3143_22182.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3143_22182.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3143_22182.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3143_22182.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3143_22182.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3143_22182.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22185 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22185 orig))
                   | uu____22188 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22206, FStar_Syntax_Syntax.Tm_abs uu____22207) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22238 -> true
                    | uu____22258 -> false in
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
                      (let uu____22318 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3105_22326 = env in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3105_22326.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3105_22326.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3105_22326.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3105_22326.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3105_22326.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3105_22326.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3105_22326.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3105_22326.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3105_22326.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3105_22326.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3105_22326.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3105_22326.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3105_22326.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3105_22326.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3105_22326.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3105_22326.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3105_22326.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3105_22326.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3105_22326.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3105_22326.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3105_22326.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3105_22326.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3105_22326.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3105_22326.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3105_22326.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3105_22326.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3105_22326.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3105_22326.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3105_22326.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3105_22326.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3105_22326.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3105_22326.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3105_22326.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3105_22326.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3105_22326.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3105_22326.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3105_22326.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3105_22326.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3105_22326.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3105_22326.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3105_22326.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3105_22326.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3105_22326.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3105_22326.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t in
                       match uu____22318 with
                       | (uu____22331, ty, uu____22333) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1 in
                               let uu____22342 =
                                 let uu____22343 =
                                   FStar_Syntax_Subst.compress ty2 in
                                 uu____22343.FStar_Syntax_Syntax.n in
                               match uu____22342 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22346 ->
                                   let uu____22353 =
                                     FStar_Syntax_Util.unrefine ty2 in
                                   aux uu____22353
                               | uu____22354 -> ty2 in
                             aux ty in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1 in
                           ((let uu____22357 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel") in
                             if uu____22357
                             then
                               let uu____22362 =
                                 FStar_Syntax_Print.term_to_string t in
                               let uu____22364 =
                                 let uu____22366 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1 in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22366 in
                               let uu____22367 =
                                 FStar_Syntax_Print.term_to_string r1 in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22362 uu____22364 uu____22367
                             else ());
                            r1)) in
                  let uu____22372 =
                    let uu____22389 = maybe_eta t1 in
                    let uu____22396 = maybe_eta t2 in
                    (uu____22389, uu____22396) in
                  (match uu____22372 with
                   | (FStar_Util.Inl t11, FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3126_22438 = problem in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3126_22438.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3126_22438.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3126_22438.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3126_22438.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3126_22438.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3126_22438.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3126_22438.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3126_22438.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs, FStar_Util.Inr not_abs) ->
                       let uu____22459 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22459
                       then
                         let uu____22462 = destruct_flex_t not_abs wl in
                         (match uu____22462 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3143_22479 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3143_22479.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3143_22479.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3143_22479.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3143_22479.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3143_22479.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3143_22479.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3143_22479.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3143_22479.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22482 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22482 orig))
                   | (FStar_Util.Inr not_abs, FStar_Util.Inl t_abs) ->
                       let uu____22505 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ) in
                       if uu____22505
                       then
                         let uu____22508 = destruct_flex_t not_abs wl in
                         (match uu____22508 with
                          | (flex, wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1 in
                          let t21 = force_eta t2 in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3143_22525 = problem in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3143_22525.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3143_22525.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3143_22525.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3143_22525.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3143_22525.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3143_22525.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3143_22525.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3143_22525.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22528 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction" in
                             giveup env uu____22528 orig))
                   | uu____22531 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine (x1, phi1),
                 FStar_Syntax_Syntax.Tm_refine (x2, phi2)) ->
                  let uu____22561 =
                    let uu____22566 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort in
                    match uu____22566 with
                    | (FullMatch, FStar_Pervasives_Native.Some (t11, t21)) ->
                        ((let uu___3166_22594 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3166_22594.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3166_22594.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3168_22596 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3168_22596.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3168_22596.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22597, FStar_Pervasives_Native.Some
                       (t11, t21)) ->
                        ((let uu___3166_22612 = x1 in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3166_22612.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3166_22612.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3168_22614 = x2 in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3168_22614.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3168_22614.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22615 -> (x1, x2) in
                  (match uu____22561 with
                   | (x11, x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1 in
                       let t21 = FStar_Syntax_Util.refine x21 phi2 in
                       let uu____22634 = as_refinement false env t11 in
                       (match uu____22634 with
                        | (x12, phi11) ->
                            let uu____22642 = as_refinement false env t21 in
                            (match uu____22642 with
                             | (x22, phi21) ->
                                 ((let uu____22651 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel") in
                                   if uu____22651
                                   then
                                     ((let uu____22656 =
                                         FStar_Syntax_Print.bv_to_string x12 in
                                       let uu____22658 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort in
                                       let uu____22660 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11 in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22656
                                         uu____22658 uu____22660);
                                      (let uu____22663 =
                                         FStar_Syntax_Print.bv_to_string x22 in
                                       let uu____22665 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort in
                                       let uu____22667 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21 in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22663
                                         uu____22665 uu____22667))
                                   else ());
                                  (let uu____22672 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type" in
                                   match uu____22672 with
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
                                         let uu____22743 = imp phi13 phi23 in
                                         FStar_All.pipe_right uu____22743
                                           (guard_on_element wl1 problem x13) in
                                       let fallback uu____22755 =
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
                                         (let uu____22768 =
                                            let uu____22771 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22771 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22768
                                            (p_guard base_prob));
                                         (let uu____22790 =
                                            let uu____22793 = p_scope orig in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22793 in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22790
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1 in
                                          let uu____22812 =
                                            attempt [base_prob] wl2 in
                                          solve env1 uu____22812) in
                                       let has_uvars =
                                         (let uu____22817 =
                                            let uu____22819 =
                                              FStar_Syntax_Free.uvars phi12 in
                                            FStar_Util.set_is_empty
                                              uu____22819 in
                                          Prims.op_Negation uu____22817) ||
                                           (let uu____22823 =
                                              let uu____22825 =
                                                FStar_Syntax_Free.uvars phi22 in
                                              FStar_Util.set_is_empty
                                                uu____22825 in
                                            Prims.op_Negation uu____22823) in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22829 =
                                           let uu____22834 =
                                             let uu____22843 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13 in
                                             [uu____22843] in
                                           mk_t_problem wl1 uu____22834 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula" in
                                         (match uu____22829 with
                                          | (ref_prob, wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  () in
                                              let uu____22866 =
                                                solve env1
                                                  (let uu___3211_22868 = wl2 in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3211_22868.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3211_22868.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3211_22868.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3211_22868.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3211_22868.tcenv);
                                                     wl_implicits =
                                                       (uu___3211_22868.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3211_22868.repr_subcomp_allowed)
                                                   }) in
                                              (match uu____22866 with
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
                                                   (uu____22883,
                                                    defer_to_tac,
                                                    uu____22885)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22890 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13) in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22890 in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2 in
                                                     let wl4 =
                                                       let uu___3227_22899 =
                                                         wl3 in
                                                       {
                                                         attempting =
                                                           (uu___3227_22899.attempting);
                                                         wl_deferred =
                                                           (uu___3227_22899.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3227_22899.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3227_22899.defer_ok);
                                                         smt_ok =
                                                           (uu___3227_22899.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3227_22899.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3227_22899.tcenv);
                                                         wl_implicits =
                                                           (uu___3227_22899.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3227_22899.repr_subcomp_allowed)
                                                       } in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac [] in
                                                     let uu____22902 =
                                                       attempt [base_prob]
                                                         wl5 in
                                                     solve env1 uu____22902))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar uu____22905,
                 FStar_Syntax_Syntax.Tm_uvar uu____22906) ->
                  let uu____22931 = ensure_no_uvar_subst t1 wl in
                  (match uu____22931 with
                   | (t11, wl1) ->
                       let uu____22938 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____22938 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22947;
                    FStar_Syntax_Syntax.pos = uu____22948;
                    FStar_Syntax_Syntax.vars = uu____22949;_},
                  uu____22950),
                 FStar_Syntax_Syntax.Tm_uvar uu____22951) ->
                  let uu____23000 = ensure_no_uvar_subst t1 wl in
                  (match uu____23000 with
                   | (t11, wl1) ->
                       let uu____23007 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____23007 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23016,
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23017;
                    FStar_Syntax_Syntax.pos = uu____23018;
                    FStar_Syntax_Syntax.vars = uu____23019;_},
                  uu____23020)) ->
                  let uu____23069 = ensure_no_uvar_subst t1 wl in
                  (match uu____23069 with
                   | (t11, wl1) ->
                       let uu____23076 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____23076 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23085;
                    FStar_Syntax_Syntax.pos = uu____23086;
                    FStar_Syntax_Syntax.vars = uu____23087;_},
                  uu____23088),
                 FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23089;
                    FStar_Syntax_Syntax.pos = uu____23090;
                    FStar_Syntax_Syntax.vars = uu____23091;_},
                  uu____23092)) ->
                  let uu____23165 = ensure_no_uvar_subst t1 wl in
                  (match uu____23165 with
                   | (t11, wl1) ->
                       let uu____23172 = ensure_no_uvar_subst t2 wl1 in
                       (match uu____23172 with
                        | (t21, wl2) ->
                            let f1 = destruct_flex_t' t11 in
                            let f2 = destruct_flex_t' t21 in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23181, uu____23182) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23195 = destruct_flex_t t1 wl in
                  (match uu____23195 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23202;
                    FStar_Syntax_Syntax.pos = uu____23203;
                    FStar_Syntax_Syntax.vars = uu____23204;_},
                  uu____23205),
                 uu____23206) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23243 = destruct_flex_t t1 wl in
                  (match uu____23243 with
                   | (f1, wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23250, FStar_Syntax_Syntax.Tm_uvar uu____23251) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23264, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23265;
                    FStar_Syntax_Syntax.pos = uu____23266;
                    FStar_Syntax_Syntax.vars = uu____23267;_},
                  uu____23268)) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar uu____23305,
                 FStar_Syntax_Syntax.Tm_arrow uu____23306) ->
                  solve_t' env
                    (let uu___3330_23334 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3330_23334.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3330_23334.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3330_23334.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3330_23334.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3330_23334.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3330_23334.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3330_23334.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3330_23334.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3330_23334.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23335;
                    FStar_Syntax_Syntax.pos = uu____23336;
                    FStar_Syntax_Syntax.vars = uu____23337;_},
                  uu____23338),
                 FStar_Syntax_Syntax.Tm_arrow uu____23339) ->
                  solve_t' env
                    (let uu___3330_23391 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3330_23391.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3330_23391.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3330_23391.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3330_23391.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3330_23391.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3330_23391.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3330_23391.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3330_23391.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3330_23391.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23392, FStar_Syntax_Syntax.Tm_uvar uu____23393) ->
                  let uu____23406 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23406
              | (uu____23407, FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23408;
                    FStar_Syntax_Syntax.pos = uu____23409;
                    FStar_Syntax_Syntax.vars = uu____23410;_},
                  uu____23411)) ->
                  let uu____23448 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23448
              | (FStar_Syntax_Syntax.Tm_uvar uu____23449, uu____23450) ->
                  let uu____23463 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23463
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23464;
                    FStar_Syntax_Syntax.pos = uu____23465;
                    FStar_Syntax_Syntax.vars = uu____23466;_},
                  uu____23467),
                 uu____23468) ->
                  let uu____23505 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl in
                  solve env uu____23505
              | (FStar_Syntax_Syntax.Tm_refine uu____23506, uu____23507) ->
                  let t21 =
                    let uu____23515 = base_and_refinement env t2 in
                    FStar_All.pipe_left force_refinement uu____23515 in
                  solve_t env
                    (let uu___3365_23541 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3365_23541.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3365_23541.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3365_23541.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3365_23541.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3365_23541.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3365_23541.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3365_23541.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3365_23541.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3365_23541.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23542, FStar_Syntax_Syntax.Tm_refine uu____23543) ->
                  let t11 =
                    let uu____23551 = base_and_refinement env t1 in
                    FStar_All.pipe_left force_refinement uu____23551 in
                  solve_t env
                    (let uu___3372_23577 = problem in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3372_23577.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3372_23577.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3372_23577.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3372_23577.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3372_23577.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3372_23577.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3372_23577.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3372_23577.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3372_23577.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match (s1, brs1),
                 FStar_Syntax_Syntax.Tm_match (s2, brs2)) ->
                  let by_smt uu____23659 =
                    let uu____23660 = guard_of_prob env wl problem t1 t2 in
                    match uu____23660 with
                    | (guard, wl1) ->
                        let uu____23667 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1 in
                        solve env uu____23667 in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1, br2::rs2) ->
                        let uu____23886 = br1 in
                        (match uu____23886 with
                         | (p1, w1, uu____23915) ->
                             let uu____23932 = br2 in
                             (match uu____23932 with
                              | (p2, w2, uu____23955) ->
                                  let uu____23960 =
                                    let uu____23962 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2 in
                                    Prims.op_Negation uu____23962 in
                                  if uu____23960
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23989 =
                                       FStar_Syntax_Subst.open_branch' br1 in
                                     match uu____23989 with
                                     | ((p11, w11, e1), s) ->
                                         let uu____24026 = br2 in
                                         (match uu____24026 with
                                          | (p21, w21, e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s) in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2 in
                                              let scope =
                                                let uu____24059 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11 in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____24059 in
                                              let uu____24064 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____24095,
                                                   FStar_Pervasives_Native.None)
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None,
                                                   FStar_Pervasives_Native.Some
                                                   uu____24116) ->
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
                                                    let uu____24175 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause" in
                                                    (match uu____24175 with
                                                     | (p, wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2)) in
                                              FStar_Util.bind_opt uu____24064
                                                (fun uu____24247 ->
                                                   match uu____24247 with
                                                   | (wprobs, wl2) ->
                                                       let uu____24284 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body" in
                                                       (match uu____24284
                                                        with
                                                        | (prob, wl3) ->
                                                            ((let uu____24305
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel") in
                                                              if uu____24305
                                                              then
                                                                let uu____24310
                                                                  =
                                                                  prob_to_string
                                                                    env prob in
                                                                let uu____24312
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24310
                                                                  uu____24312
                                                              else ());
                                                             (let uu____24318
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2 in
                                                              FStar_Util.bind_opt
                                                                uu____24318
                                                                (fun
                                                                   uu____24354
                                                                   ->
                                                                   match uu____24354
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
                    | uu____24483 -> FStar_Pervasives_Native.None in
                  let uu____24524 = solve_branches wl brs1 brs2 in
                  (match uu____24524 with
                   | FStar_Pervasives_Native.None ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24550 =
                            FStar_Thunk.mkv "Tm_match branches don't match" in
                          giveup env uu____24550 orig)
                   | FStar_Pervasives_Native.Some (sub_probs, wl1) ->
                       let uu____24577 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee" in
                       (match uu____24577 with
                        | (sc_prob, wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs in
                            let formula =
                              let uu____24611 =
                                FStar_List.map
                                  (fun uu____24623 ->
                                     match uu____24623 with
                                     | (scope, p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1 in
                              FStar_Syntax_Util.mk_conj_l uu____24611 in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction () in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2 in
                            let uu____24632 =
                              let uu____24633 =
                                let uu____24634 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1 in
                                attempt uu____24634
                                  (let uu___3471_24642 = wl3 in
                                   {
                                     attempting =
                                       (uu___3471_24642.attempting);
                                     wl_deferred =
                                       (uu___3471_24642.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3471_24642.wl_deferred_to_tac);
                                     ctr = (uu___3471_24642.ctr);
                                     defer_ok = (uu___3471_24642.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3471_24642.umax_heuristic_ok);
                                     tcenv = (uu___3471_24642.tcenv);
                                     wl_implicits =
                                       (uu___3471_24642.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3471_24642.repr_subcomp_allowed)
                                   }) in
                              solve env uu____24633 in
                            (match uu____24632 with
                             | Success (ds, ds', imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24648 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24657 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT" in
                                     giveup env uu____24657 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24660, uu____24661) ->
                  let head1 =
                    let uu____24685 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24685
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24731 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24731
                      FStar_Pervasives_Native.fst in
                  ((let uu____24777 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24777
                    then
                      let uu____24781 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24783 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24785 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24781 uu____24783 uu____24785
                    else ());
                   (let no_free_uvars t =
                      (let uu____24799 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____24799) &&
                        (let uu____24803 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____24803) in
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
                      let uu____24822 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____24822 = FStar_Syntax_Util.Equal in
                    let uu____24823 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____24823
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24827 = equal t1 t2 in
                         (if uu____24827
                          then
                            let uu____24830 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____24830
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24835 =
                            let uu____24842 = equal t1 t2 in
                            if uu____24842
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24855 = mk_eq2 wl env orig t1 t2 in
                               match uu____24855 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____24835 with
                          | (guard, wl1) ->
                              let uu____24876 = solve_prob orig guard [] wl1 in
                              solve env uu____24876))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24879, uu____24880) ->
                  let head1 =
                    let uu____24888 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____24888
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____24934 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____24934
                      FStar_Pervasives_Native.fst in
                  ((let uu____24980 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____24980
                    then
                      let uu____24984 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____24986 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____24988 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24984 uu____24986 uu____24988
                    else ());
                   (let no_free_uvars t =
                      (let uu____25002 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25002) &&
                        (let uu____25006 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25006) in
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
                      let uu____25025 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25025 = FStar_Syntax_Util.Equal in
                    let uu____25026 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25026
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25030 = equal t1 t2 in
                         (if uu____25030
                          then
                            let uu____25033 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25033
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25038 =
                            let uu____25045 = equal t1 t2 in
                            if uu____25045
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25058 = mk_eq2 wl env orig t1 t2 in
                               match uu____25058 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25038 with
                          | (guard, wl1) ->
                              let uu____25079 = solve_prob orig guard [] wl1 in
                              solve env uu____25079))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____25082, uu____25083) ->
                  let head1 =
                    let uu____25085 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25085
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25131 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25131
                      FStar_Pervasives_Native.fst in
                  ((let uu____25177 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25177
                    then
                      let uu____25181 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25183 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25185 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25181 uu____25183 uu____25185
                    else ());
                   (let no_free_uvars t =
                      (let uu____25199 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25199) &&
                        (let uu____25203 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25203) in
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
                      let uu____25222 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25222 = FStar_Syntax_Util.Equal in
                    let uu____25223 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25223
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25227 = equal t1 t2 in
                         (if uu____25227
                          then
                            let uu____25230 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25230
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25235 =
                            let uu____25242 = equal t1 t2 in
                            if uu____25242
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25255 = mk_eq2 wl env orig t1 t2 in
                               match uu____25255 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25235 with
                          | (guard, wl1) ->
                              let uu____25276 = solve_prob orig guard [] wl1 in
                              solve env uu____25276))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25279, uu____25280) ->
                  let head1 =
                    let uu____25282 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25282
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25328 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25328
                      FStar_Pervasives_Native.fst in
                  ((let uu____25374 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25374
                    then
                      let uu____25378 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25380 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25382 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25378 uu____25380 uu____25382
                    else ());
                   (let no_free_uvars t =
                      (let uu____25396 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25396) &&
                        (let uu____25400 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25400) in
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
                      let uu____25419 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25419 = FStar_Syntax_Util.Equal in
                    let uu____25420 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25420
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25424 = equal t1 t2 in
                         (if uu____25424
                          then
                            let uu____25427 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25427
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25432 =
                            let uu____25439 = equal t1 t2 in
                            if uu____25439
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25452 = mk_eq2 wl env orig t1 t2 in
                               match uu____25452 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25432 with
                          | (guard, wl1) ->
                              let uu____25473 = solve_prob orig guard [] wl1 in
                              solve env uu____25473))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25476, uu____25477) ->
                  let head1 =
                    let uu____25479 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25479
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25519 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25519
                      FStar_Pervasives_Native.fst in
                  ((let uu____25559 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25559
                    then
                      let uu____25563 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25565 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25567 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25563 uu____25565 uu____25567
                    else ());
                   (let no_free_uvars t =
                      (let uu____25581 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25581) &&
                        (let uu____25585 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25585) in
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
                      let uu____25604 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25604 = FStar_Syntax_Util.Equal in
                    let uu____25605 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25605
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25609 = equal t1 t2 in
                         (if uu____25609
                          then
                            let uu____25612 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25612
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25617 =
                            let uu____25624 = equal t1 t2 in
                            if uu____25624
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25637 = mk_eq2 wl env orig t1 t2 in
                               match uu____25637 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25617 with
                          | (guard, wl1) ->
                              let uu____25658 = solve_prob orig guard [] wl1 in
                              solve env uu____25658))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25661, uu____25662) ->
                  let head1 =
                    let uu____25680 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25680
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25720 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25720
                      FStar_Pervasives_Native.fst in
                  ((let uu____25760 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25760
                    then
                      let uu____25764 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25766 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25768 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25764 uu____25766 uu____25768
                    else ());
                   (let no_free_uvars t =
                      (let uu____25782 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25782) &&
                        (let uu____25786 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25786) in
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
                      let uu____25805 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____25805 = FStar_Syntax_Util.Equal in
                    let uu____25806 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____25806
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25810 = equal t1 t2 in
                         (if uu____25810
                          then
                            let uu____25813 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____25813
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25818 =
                            let uu____25825 = equal t1 t2 in
                            if uu____25825
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25838 = mk_eq2 wl env orig t1 t2 in
                               match uu____25838 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____25818 with
                          | (guard, wl1) ->
                              let uu____25859 = solve_prob orig guard [] wl1 in
                              solve env uu____25859))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25862, FStar_Syntax_Syntax.Tm_match uu____25863) ->
                  let head1 =
                    let uu____25887 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____25887
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____25927 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____25927
                      FStar_Pervasives_Native.fst in
                  ((let uu____25967 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____25967
                    then
                      let uu____25971 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____25973 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____25975 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25971 uu____25973 uu____25975
                    else ());
                   (let no_free_uvars t =
                      (let uu____25989 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____25989) &&
                        (let uu____25993 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____25993) in
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
                      let uu____26012 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26012 = FStar_Syntax_Util.Equal in
                    let uu____26013 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26013
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26017 = equal t1 t2 in
                         (if uu____26017
                          then
                            let uu____26020 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26020
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26025 =
                            let uu____26032 = equal t1 t2 in
                            if uu____26032
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26045 = mk_eq2 wl env orig t1 t2 in
                               match uu____26045 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26025 with
                          | (guard, wl1) ->
                              let uu____26066 = solve_prob orig guard [] wl1 in
                              solve env uu____26066))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26069, FStar_Syntax_Syntax.Tm_uinst uu____26070) ->
                  let head1 =
                    let uu____26078 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26078
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26118 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26118
                      FStar_Pervasives_Native.fst in
                  ((let uu____26158 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26158
                    then
                      let uu____26162 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26164 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26166 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26162 uu____26164 uu____26166
                    else ());
                   (let no_free_uvars t =
                      (let uu____26180 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26180) &&
                        (let uu____26184 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26184) in
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
                      let uu____26203 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26203 = FStar_Syntax_Util.Equal in
                    let uu____26204 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26204
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26208 = equal t1 t2 in
                         (if uu____26208
                          then
                            let uu____26211 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26211
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26216 =
                            let uu____26223 = equal t1 t2 in
                            if uu____26223
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26236 = mk_eq2 wl env orig t1 t2 in
                               match uu____26236 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26216 with
                          | (guard, wl1) ->
                              let uu____26257 = solve_prob orig guard [] wl1 in
                              solve env uu____26257))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26260, FStar_Syntax_Syntax.Tm_name uu____26261) ->
                  let head1 =
                    let uu____26263 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26263
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26303 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26303
                      FStar_Pervasives_Native.fst in
                  ((let uu____26343 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26343
                    then
                      let uu____26347 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26349 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26351 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26347 uu____26349 uu____26351
                    else ());
                   (let no_free_uvars t =
                      (let uu____26365 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26365) &&
                        (let uu____26369 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26369) in
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
                      let uu____26388 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26388 = FStar_Syntax_Util.Equal in
                    let uu____26389 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26389
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26393 = equal t1 t2 in
                         (if uu____26393
                          then
                            let uu____26396 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26396
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26401 =
                            let uu____26408 = equal t1 t2 in
                            if uu____26408
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26421 = mk_eq2 wl env orig t1 t2 in
                               match uu____26421 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26401 with
                          | (guard, wl1) ->
                              let uu____26442 = solve_prob orig guard [] wl1 in
                              solve env uu____26442))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26445, FStar_Syntax_Syntax.Tm_constant uu____26446) ->
                  let head1 =
                    let uu____26448 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26448
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26488 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26488
                      FStar_Pervasives_Native.fst in
                  ((let uu____26528 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26528
                    then
                      let uu____26532 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26534 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26536 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26532 uu____26534 uu____26536
                    else ());
                   (let no_free_uvars t =
                      (let uu____26550 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26550) &&
                        (let uu____26554 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26554) in
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
                      let uu____26573 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26573 = FStar_Syntax_Util.Equal in
                    let uu____26574 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26574
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26578 = equal t1 t2 in
                         (if uu____26578
                          then
                            let uu____26581 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26581
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26586 =
                            let uu____26593 = equal t1 t2 in
                            if uu____26593
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26606 = mk_eq2 wl env orig t1 t2 in
                               match uu____26606 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26586 with
                          | (guard, wl1) ->
                              let uu____26627 = solve_prob orig guard [] wl1 in
                              solve env uu____26627))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26630, FStar_Syntax_Syntax.Tm_fvar uu____26631) ->
                  let head1 =
                    let uu____26633 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26633
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26679 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26679
                      FStar_Pervasives_Native.fst in
                  ((let uu____26725 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26725
                    then
                      let uu____26729 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26731 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26733 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26729 uu____26731 uu____26733
                    else ());
                   (let no_free_uvars t =
                      (let uu____26747 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26747) &&
                        (let uu____26751 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26751) in
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
                      let uu____26770 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26770 = FStar_Syntax_Util.Equal in
                    let uu____26771 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26771
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26775 = equal t1 t2 in
                         (if uu____26775
                          then
                            let uu____26778 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26778
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26783 =
                            let uu____26790 = equal t1 t2 in
                            if uu____26790
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26803 = mk_eq2 wl env orig t1 t2 in
                               match uu____26803 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26783 with
                          | (guard, wl1) ->
                              let uu____26824 = solve_prob orig guard [] wl1 in
                              solve env uu____26824))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26827, FStar_Syntax_Syntax.Tm_app uu____26828) ->
                  let head1 =
                    let uu____26846 = FStar_Syntax_Util.head_and_args t1 in
                    FStar_All.pipe_right uu____26846
                      FStar_Pervasives_Native.fst in
                  let head2 =
                    let uu____26886 = FStar_Syntax_Util.head_and_args t2 in
                    FStar_All.pipe_right uu____26886
                      FStar_Pervasives_Native.fst in
                  ((let uu____26926 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel") in
                    if uu____26926
                    then
                      let uu____26930 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid in
                      let uu____26932 =
                        FStar_Syntax_Print.term_to_string head1 in
                      let uu____26934 =
                        FStar_Syntax_Print.term_to_string head2 in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26930 uu____26932 uu____26934
                    else ());
                   (let no_free_uvars t =
                      (let uu____26948 = FStar_Syntax_Free.uvars t in
                       FStar_Util.set_is_empty uu____26948) &&
                        (let uu____26952 = FStar_Syntax_Free.univs t in
                         FStar_Util.set_is_empty uu____26952) in
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
                      let uu____26971 = FStar_Syntax_Util.eq_tm t12 t22 in
                      uu____26971 = FStar_Syntax_Util.Equal in
                    let uu____26972 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2) in
                    if uu____26972
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26976 = equal t1 t2 in
                         (if uu____26976
                          then
                            let uu____26979 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl in
                            solve env uu____26979
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26984 =
                            let uu____26991 = equal t1 t2 in
                            if uu____26991
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____27004 = mk_eq2 wl env orig t1 t2 in
                               match uu____27004 with
                               | (g, wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1)) in
                          match uu____26984 with
                          | (guard, wl1) ->
                              let uu____27025 = solve_prob orig guard [] wl1 in
                              solve env uu____27025))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let uu____27028,
                 FStar_Syntax_Syntax.Tm_let uu____27029) ->
                  let uu____27056 = FStar_Syntax_Util.term_eq t1 t2 in
                  if uu____27056
                  then
                    let uu____27059 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl in
                    solve env uu____27059
                  else
                    (let uu____27062 = FStar_Thunk.mkv "Tm_let mismatch" in
                     giveup env uu____27062 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____27065, uu____27066) ->
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
              | (uu____27098, FStar_Syntax_Syntax.Tm_let uu____27099) ->
                  let uu____27113 =
                    let uu____27119 =
                      let uu____27121 = FStar_Syntax_Print.tag_of_term t1 in
                      let uu____27123 = FStar_Syntax_Print.tag_of_term t2 in
                      let uu____27125 = FStar_Syntax_Print.term_to_string t1 in
                      let uu____27127 = FStar_Syntax_Print.term_to_string t2 in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27121 uu____27123 uu____27125 uu____27127 in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27119) in
                  FStar_Errors.raise_error uu____27113
                    t1.FStar_Syntax_Syntax.pos
              | uu____27131 ->
                  let uu____27136 = FStar_Thunk.mkv "head tag mismatch" in
                  giveup env uu____27136 orig))))
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
          (let uu____27202 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ") in
           if uu____27202
           then
             let uu____27207 =
               let uu____27209 = FStar_Syntax_Syntax.mk_Comp c1_comp in
               FStar_Syntax_Print.comp_to_string uu____27209 in
             let uu____27210 =
               let uu____27212 = FStar_Syntax_Syntax.mk_Comp c2_comp in
               FStar_Syntax_Print.comp_to_string uu____27212 in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27207 uu____27210
           else ());
          (let uu____27216 =
             let uu____27218 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name in
             Prims.op_Negation uu____27218 in
           if uu____27216
           then
             let uu____27221 =
               mklstr
                 (fun uu____27228 ->
                    let uu____27229 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name in
                    let uu____27231 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27229 uu____27231) in
             giveup env uu____27221 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27253 =
                  mklstr
                    (fun uu____27260 ->
                       let uu____27261 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args in
                       let uu____27263 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27261 uu____27263) in
                giveup env uu____27253 orig)
             else
               (let uu____27268 =
                  FStar_List.fold_left2
                    (fun uu____27289 ->
                       fun u1 ->
                         fun u2 ->
                           match uu____27289 with
                           | (univ_sub_probs, wl1) ->
                               let uu____27310 =
                                 let uu____27315 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange in
                                 let uu____27316 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange in
                                 sub_prob wl1 uu____27315
                                   FStar_TypeChecker_Common.EQ uu____27316
                                   "effect universes" in
                               (match uu____27310 with
                                | (p, wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs in
                match uu____27268 with
                | (univ_sub_probs, wl1) ->
                    let uu____27336 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type" in
                    (match uu____27336 with
                     | (ret_sub_prob, wl2) ->
                         let uu____27344 =
                           FStar_List.fold_right2
                             (fun uu____27381 ->
                                fun uu____27382 ->
                                  fun uu____27383 ->
                                    match (uu____27381, uu____27382,
                                            uu____27383)
                                    with
                                    | ((a1, uu____27427), (a2, uu____27429),
                                       (arg_sub_probs, wl3)) ->
                                        let uu____27462 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg" in
                                        (match uu____27462 with
                                         | (p, wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2) in
                         (match uu____27344 with
                          | (arg_sub_probs, wl3) ->
                              let sub_probs =
                                let uu____27489 =
                                  let uu____27492 =
                                    let uu____27495 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd) in
                                    FStar_List.append arg_sub_probs
                                      uu____27495 in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27492 in
                                FStar_List.append univ_sub_probs uu____27489 in
                              let guard =
                                let guard =
                                  let uu____27517 =
                                    FStar_List.map p_guard sub_probs in
                                  FStar_Syntax_Util.mk_conj_l uu____27517 in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f in
                              let wl4 =
                                let uu___3624_27526 = wl3 in
                                {
                                  attempting = (uu___3624_27526.attempting);
                                  wl_deferred = (uu___3624_27526.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3624_27526.wl_deferred_to_tac);
                                  ctr = (uu___3624_27526.ctr);
                                  defer_ok = (uu___3624_27526.defer_ok);
                                  smt_ok = (uu___3624_27526.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3624_27526.umax_heuristic_ok);
                                  tcenv = (uu___3624_27526.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3624_27526.repr_subcomp_allowed)
                                } in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4 in
                              let uu____27528 = attempt sub_probs wl5 in
                              solve env uu____27528)))) in
        let solve_layered_sub c11 c21 =
          (let uu____27541 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp") in
           if uu____27541
           then
             let uu____27546 =
               let uu____27548 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____27548
                 FStar_Syntax_Print.comp_to_string in
             let uu____27550 =
               let uu____27552 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____27552
                 FStar_Syntax_Print.comp_to_string in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27546 uu____27550
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env in
             let subcomp_name =
               let uu____27563 =
                 let uu____27565 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____27565 FStar_Ident.string_of_id in
               let uu____27567 =
                 let uu____27569 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid in
                 FStar_All.pipe_right uu____27569 FStar_Ident.string_of_id in
               FStar_Util.format2 "%s <: %s" uu____27563 uu____27567 in
             let lift_c1 edge =
               let uu____27586 =
                 let uu____27591 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp in
                 FStar_All.pipe_right uu____27591
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env) in
               FStar_All.pipe_right uu____27586
                 (fun uu____27608 ->
                    match uu____27608 with
                    | (c, g) ->
                        let uu____27619 =
                          FStar_Syntax_Util.comp_to_comp_typ c in
                        (uu____27619, g)) in
             let uu____27620 =
               let uu____27632 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name in
               match uu____27632 with
               | FStar_Pervasives_Native.None ->
                   let uu____27646 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name in
                   (match uu____27646 with
                    | FStar_Pervasives_Native.None ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____27665 = lift_c1 edge in
                        (match uu____27665 with
                         | (c12, g_lift) ->
                             let uu____27683 =
                               let uu____27686 =
                                 let uu____27687 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env) in
                                 FStar_All.pipe_right uu____27687
                                   FStar_Syntax_Util.get_stronger_vc_combinator in
                               FStar_All.pipe_right uu____27686
                                 (fun ts ->
                                    let uu____27693 =
                                      let uu____27694 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs in
                                      FStar_All.pipe_right uu____27694
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____27693
                                      (fun uu____27705 ->
                                         FStar_Pervasives_Native.Some
                                           uu____27705)) in
                             (c12, g_lift, uu____27683, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____27711 =
                     let uu____27714 =
                       let uu____27715 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs in
                       FStar_All.pipe_right uu____27715
                         FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____27714
                       (fun uu____27726 ->
                          FStar_Pervasives_Native.Some uu____27726) in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____27711,
                     true) in
             match uu____27620 with
             | (c12, g_lift, stronger_t_opt, is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____27742 =
                     mklstr
                       (fun uu____27749 ->
                          let uu____27750 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name in
                          let uu____27752 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____27750 uu____27752) in
                   giveup env uu____27742 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must in
                    let wl1 =
                      let uu___3659_27761 = wl in
                      {
                        attempting = (uu___3659_27761.attempting);
                        wl_deferred = (uu___3659_27761.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3659_27761.wl_deferred_to_tac);
                        ctr = (uu___3659_27761.ctr);
                        defer_ok = (uu___3659_27761.defer_ok);
                        smt_ok = (uu___3659_27761.smt_ok);
                        umax_heuristic_ok =
                          (uu___3659_27761.umax_heuristic_ok);
                        tcenv = (uu___3659_27761.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3659_27761.repr_subcomp_allowed)
                      } in
                    let uu____27762 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____27787 =
                             let uu____27788 = FStar_Syntax_Subst.compress t in
                             uu____27788.FStar_Syntax_Syntax.n in
                           match uu____27787 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____27792 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1, uu____27807)
                               -> is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1, uu____27813) ->
                               is_uvar t1
                           | uu____27838 -> false in
                         FStar_List.fold_right2
                           (fun uu____27872 ->
                              fun uu____27873 ->
                                fun uu____27874 ->
                                  match (uu____27872, uu____27873,
                                          uu____27874)
                                  with
                                  | ((a1, uu____27918), (a2, uu____27920),
                                     (is_sub_probs, wl2)) ->
                                      let uu____27953 = is_uvar a1 in
                                      if uu____27953
                                      then
                                        ((let uu____27963 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns") in
                                          if uu____27963
                                          then
                                            let uu____27968 =
                                              FStar_Syntax_Print.term_to_string
                                                a1 in
                                            let uu____27970 =
                                              FStar_Syntax_Print.term_to_string
                                                a2 in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____27968 uu____27970
                                          else ());
                                         (let uu____27975 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar" in
                                          match uu____27975 with
                                          | (p, wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1)) in
                    match uu____27762 with
                    | (is_sub_probs, wl2) ->
                        let uu____28003 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type" in
                        (match uu____28003 with
                         | (ret_sub_prob, wl3) ->
                             let stronger_t_shape_error s =
                               let uu____28020 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name in
                               let uu____28022 =
                                 FStar_Syntax_Print.term_to_string stronger_t in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____28020 s uu____28022 in
                             let uu____28025 =
                               let uu____28054 =
                                 let uu____28055 =
                                   FStar_Syntax_Subst.compress stronger_t in
                                 uu____28055.FStar_Syntax_Syntax.n in
                               match uu____28054 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs, c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____28115 =
                                     FStar_Syntax_Subst.open_comp bs c in
                                   (match uu____28115 with
                                    | (bs', c3) ->
                                        let a = FStar_List.hd bs' in
                                        let bs1 = FStar_List.tail bs' in
                                        let uu____28178 =
                                          let uu____28197 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one)) in
                                          FStar_All.pipe_right uu____28197
                                            (fun uu____28301 ->
                                               match uu____28301 with
                                               | (l1, l2) ->
                                                   let uu____28374 =
                                                     FStar_List.hd l2 in
                                                   (l1, uu____28374)) in
                                        (match uu____28178 with
                                         | (rest_bs, f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____28479 ->
                                   let uu____28480 =
                                     let uu____28486 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders" in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____28486) in
                                   FStar_Errors.raise_error uu____28480 r in
                             (match uu____28025 with
                              | (a_b, rest_bs, f_b, stronger_c) ->
                                  let uu____28562 =
                                    let uu____28569 =
                                      let uu____28570 =
                                        let uu____28571 =
                                          let uu____28578 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst in
                                          (uu____28578,
                                            (c21.FStar_Syntax_Syntax.result_typ)) in
                                        FStar_Syntax_Syntax.NT uu____28571 in
                                      [uu____28570] in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____28569
                                      (fun b ->
                                         let uu____28594 =
                                           FStar_Syntax_Print.binder_to_string
                                             b in
                                         let uu____28596 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name in
                                         let uu____28598 =
                                           FStar_Range.string_of_range r in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____28594 uu____28596
                                           uu____28598) r in
                                  (match uu____28562 with
                                   | (rest_bs_uvars, g_uvars) ->
                                       let wl4 =
                                         let uu___3724_28608 = wl3 in
                                         {
                                           attempting =
                                             (uu___3724_28608.attempting);
                                           wl_deferred =
                                             (uu___3724_28608.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3724_28608.wl_deferred_to_tac);
                                           ctr = (uu___3724_28608.ctr);
                                           defer_ok =
                                             (uu___3724_28608.defer_ok);
                                           smt_ok = (uu___3724_28608.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3724_28608.umax_heuristic_ok);
                                           tcenv = (uu___3724_28608.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3724_28608.repr_subcomp_allowed)
                                         } in
                                       let substs =
                                         FStar_List.map2
                                           (fun b ->
                                              fun t ->
                                                let uu____28633 =
                                                  let uu____28640 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst in
                                                  (uu____28640, t) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____28633) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars) in
                                       let uu____28657 =
                                         let f_sort_is =
                                           let uu____28667 =
                                             let uu____28670 =
                                               let uu____28671 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst in
                                               uu____28671.FStar_Syntax_Syntax.sort in
                                             let uu____28680 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name in
                                             let uu____28682 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type" in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____28670 uu____28680 r
                                               uu____28682 in
                                           FStar_All.pipe_right uu____28667
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs)) in
                                         let uu____28689 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_List.fold_left2
                                           (fun uu____28725 ->
                                              fun f_sort_i ->
                                                fun c1_i ->
                                                  match uu____28725 with
                                                  | (ps, wl5) ->
                                                      ((let uu____28747 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns") in
                                                        if uu____28747
                                                        then
                                                          let uu____28752 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i in
                                                          let uu____28754 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____28752
                                                            uu____28754
                                                        else ());
                                                       (let uu____28759 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1" in
                                                        match uu____28759
                                                        with
                                                        | (p, wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____28689 in
                                       (match uu____28657 with
                                        | (f_sub_probs, wl5) ->
                                            let stronger_ct =
                                              let uu____28784 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs) in
                                              FStar_All.pipe_right
                                                uu____28784
                                                FStar_Syntax_Util.comp_to_comp_typ in
                                            let uu____28785 =
                                              let g_sort_is =
                                                let uu____28795 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name in
                                                let uu____28797 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr" in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____28795 r uu____28797 in
                                              let uu____28800 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst) in
                                              FStar_List.fold_left2
                                                (fun uu____28836 ->
                                                   fun g_sort_i ->
                                                     fun c2_i ->
                                                       match uu____28836 with
                                                       | (ps, wl6) ->
                                                           ((let uu____28858
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns") in
                                                             if uu____28858
                                                             then
                                                               let uu____28863
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i in
                                                               let uu____28865
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____28863
                                                                 uu____28865
                                                             else ());
                                                            (let uu____28870
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2" in
                                                             match uu____28870
                                                             with
                                                             | (p, wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____28800 in
                                            (match uu____28785 with
                                             | (g_sub_probs, wl6) ->
                                                 let fml =
                                                   let uu____28897 =
                                                     let uu____28902 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs in
                                                     let uu____28903 =
                                                       let uu____28904 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args in
                                                       FStar_Pervasives_Native.fst
                                                         uu____28904 in
                                                     (uu____28902,
                                                       uu____28903) in
                                                   match uu____28897 with
                                                   | (u, wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange in
                                                 let sub_probs =
                                                   let uu____28932 =
                                                     let uu____28935 =
                                                       let uu____28938 =
                                                         let uu____28941 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd) in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____28941 in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____28938 in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____28935 in
                                                   ret_sub_prob ::
                                                     uu____28932 in
                                                 let guard =
                                                   let guard =
                                                     let uu____28965 =
                                                       FStar_List.map p_guard
                                                         sub_probs in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____28965 in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                       -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f in
                                                 let wl7 =
                                                   let uu____28976 =
                                                     let uu____28979 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml in
                                                     FStar_All.pipe_left
                                                       (fun uu____28982 ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____28982)
                                                       uu____28979 in
                                                   solve_prob orig
                                                     uu____28976 [] wl6 in
                                                 let uu____28983 =
                                                   attempt sub_probs wl7 in
                                                 solve env uu____28983))))))) in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env in
           let lift_c1 uu____29011 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____29013 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ in
                   [uu____29013]
               | x -> x in
             let c12 =
               let uu___3782_29016 = c11 in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3782_29016.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3782_29016.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3782_29016.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3782_29016.FStar_Syntax_Syntax.flags)
               } in
             let uu____29017 =
               let uu____29022 =
                 FStar_All.pipe_right
                   (let uu___3785_29024 = c12 in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3785_29024.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3785_29024.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3785_29024.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3785_29024.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp in
               FStar_All.pipe_right uu____29022
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env) in
             FStar_All.pipe_right uu____29017
               (fun uu____29038 ->
                  match uu____29038 with
                  | (c, g) ->
                      let uu____29045 =
                        let uu____29047 = FStar_TypeChecker_Env.is_trivial g in
                        Prims.op_Negation uu____29047 in
                      if uu____29045
                      then
                        let uu____29050 =
                          let uu____29056 =
                            let uu____29058 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name in
                            let uu____29060 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____29058 uu____29060 in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____29056) in
                        FStar_Errors.raise_error uu____29050 r
                      else FStar_Syntax_Util.comp_to_comp_typ c) in
           let uu____29066 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____29069 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name in
                 Prims.op_Negation uu____29069))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name) in
           if uu____29066
           then
             let uu____29072 =
               mklstr
                 (fun uu____29079 ->
                    let uu____29080 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name in
                    let uu____29082 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____29080 uu____29082) in
             giveup env uu____29072 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_29093 ->
                        match uu___29_29093 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | FStar_Syntax_Syntax.MLEFFECT -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL -> true
                        | uu____29098 -> false)) in
              let uu____29100 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1, uu____29130)::uu____29131,
                   (wp2, uu____29133)::uu____29134) -> (wp1, wp2)
                | uu____29207 ->
                    let uu____29232 =
                      let uu____29238 =
                        let uu____29240 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name in
                        let uu____29242 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____29240 uu____29242 in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____29238) in
                    FStar_Errors.raise_error uu____29232
                      env.FStar_TypeChecker_Env.range in
              match uu____29100 with
              | (wpc1, wpc2) ->
                  let uu____29252 = FStar_Util.physical_equality wpc1 wpc2 in
                  if uu____29252
                  then
                    let uu____29255 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type" in
                    solve_t env uu____29255 wl
                  else
                    (let uu____29259 =
                       let uu____29266 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name in
                       FStar_Util.must uu____29266 in
                     match uu____29259 with
                     | (c2_decl, qualifiers) ->
                         let uu____29287 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable) in
                         if uu____29287
                         then
                           let c1_repr =
                             let uu____29294 =
                               let uu____29295 =
                                 let uu____29296 = lift_c1 () in
                                 FStar_Syntax_Syntax.mk_Comp uu____29296 in
                               let uu____29297 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____29295 uu____29297 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____29294 in
                           let c2_repr =
                             let uu____29300 =
                               let uu____29301 =
                                 FStar_Syntax_Syntax.mk_Comp c21 in
                               let uu____29302 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____29301 uu____29302 in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____29300 in
                           let uu____29304 =
                             let uu____29309 =
                               let uu____29311 =
                                 FStar_Syntax_Print.term_to_string c1_repr in
                               let uu____29313 =
                                 FStar_Syntax_Print.term_to_string c2_repr in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____29311 uu____29313 in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____29309 in
                           (match uu____29304 with
                            | (prob, wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1 in
                                let uu____29319 = attempt [prob] wl2 in
                                solve env uu____29319)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____29339 = lift_c1 () in
                                   FStar_All.pipe_right uu____29339
                                     (fun ct ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args) in
                                 if is_null_wp_2
                                 then
                                   ((let uu____29362 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel") in
                                     if uu____29362
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ in
                                     let trivial =
                                       let uu____29372 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator in
                                       match uu____29372 with
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t in
                                     let uu____29379 =
                                       let uu____29380 =
                                         let uu____29397 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial in
                                         let uu____29400 =
                                           let uu____29411 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ in
                                           [uu____29411; wpc1_2] in
                                         (uu____29397, uu____29400) in
                                       FStar_Syntax_Syntax.Tm_app uu____29380 in
                                     FStar_Syntax_Syntax.mk uu____29379 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator in
                                    let uu____29460 =
                                      let uu____29461 =
                                        let uu____29478 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger in
                                        let uu____29481 =
                                          let uu____29492 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ in
                                          let uu____29501 =
                                            let uu____29512 =
                                              FStar_Syntax_Syntax.as_arg wpc2 in
                                            [uu____29512; wpc1_2] in
                                          uu____29492 :: uu____29501 in
                                        (uu____29478, uu____29481) in
                                      FStar_Syntax_Syntax.Tm_app uu____29461 in
                                    FStar_Syntax_Syntax.mk uu____29460 r)) in
                            (let uu____29566 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel") in
                             if uu____29566
                             then
                               let uu____29571 =
                                 let uu____29573 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g in
                                 FStar_Syntax_Print.term_to_string
                                   uu____29573 in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____29571
                             else ());
                            (let uu____29577 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type" in
                             match uu____29577 with
                             | (base_prob, wl1) ->
                                 let wl2 =
                                   let uu____29586 =
                                     let uu____29589 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g in
                                     FStar_All.pipe_left
                                       (fun uu____29592 ->
                                          FStar_Pervasives_Native.Some
                                            uu____29592) uu____29589 in
                                   solve_prob orig uu____29586 [] wl1 in
                                 let uu____29593 = attempt [base_prob] wl2 in
                                 solve env uu____29593))))) in
        let uu____29594 = FStar_Util.physical_equality c1 c2 in
        if uu____29594
        then
          let uu____29597 =
            solve_prob orig FStar_Pervasives_Native.None [] wl in
          solve env uu____29597
        else
          ((let uu____29601 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel") in
            if uu____29601
            then
              let uu____29606 = FStar_Syntax_Print.comp_to_string c1 in
              let uu____29608 = FStar_Syntax_Print.comp_to_string c2 in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29606
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29608
            else ());
           (let uu____29613 =
              let uu____29622 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1 in
              let uu____29625 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2 in
              (uu____29622, uu____29625) in
            match uu____29613 with
            | (c11, c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____29643),
                    FStar_Syntax_Syntax.Total (t2, uu____29645)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29662 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29662 wl
                 | (FStar_Syntax_Syntax.GTotal uu____29664,
                    FStar_Syntax_Syntax.Total uu____29665) ->
                     let uu____29682 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot" in
                     giveup env uu____29682 orig
                 | (FStar_Syntax_Syntax.Total (t1, uu____29686),
                    FStar_Syntax_Syntax.Total (t2, uu____29688)) ->
                     let uu____29705 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29705 wl
                 | (FStar_Syntax_Syntax.GTotal (t1, uu____29708),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29710)) ->
                     let uu____29727 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29727 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____29730),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29732)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29749 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type" in
                     solve_t env uu____29749 wl
                 | (FStar_Syntax_Syntax.Total (t1, uu____29752),
                    FStar_Syntax_Syntax.GTotal (t2, uu____29754)) ->
                     let uu____29771 = FStar_Thunk.mkv "GTot =/= Tot" in
                     giveup env uu____29771 orig
                 | (FStar_Syntax_Syntax.GTotal uu____29774,
                    FStar_Syntax_Syntax.Comp uu____29775) ->
                     let uu____29784 =
                       let uu___3909_29787 = problem in
                       let uu____29790 =
                         let uu____29791 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29791 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3909_29787.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29790;
                         FStar_TypeChecker_Common.relation =
                           (uu___3909_29787.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3909_29787.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3909_29787.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3909_29787.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3909_29787.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3909_29787.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3909_29787.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3909_29787.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29784 wl
                 | (FStar_Syntax_Syntax.Total uu____29792,
                    FStar_Syntax_Syntax.Comp uu____29793) ->
                     let uu____29802 =
                       let uu___3909_29805 = problem in
                       let uu____29808 =
                         let uu____29809 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29809 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3909_29805.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29808;
                         FStar_TypeChecker_Common.relation =
                           (uu___3909_29805.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3909_29805.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3909_29805.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3909_29805.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3909_29805.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3909_29805.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3909_29805.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3909_29805.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29802 wl
                 | (FStar_Syntax_Syntax.Comp uu____29810,
                    FStar_Syntax_Syntax.GTotal uu____29811) ->
                     let uu____29820 =
                       let uu___3921_29823 = problem in
                       let uu____29826 =
                         let uu____29827 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29827 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3921_29823.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3921_29823.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3921_29823.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29826;
                         FStar_TypeChecker_Common.element =
                           (uu___3921_29823.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3921_29823.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3921_29823.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3921_29823.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3921_29823.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3921_29823.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29820 wl
                 | (FStar_Syntax_Syntax.Comp uu____29828,
                    FStar_Syntax_Syntax.Total uu____29829) ->
                     let uu____29838 =
                       let uu___3921_29841 = problem in
                       let uu____29844 =
                         let uu____29845 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29845 in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3921_29841.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3921_29841.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3921_29841.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29844;
                         FStar_TypeChecker_Common.element =
                           (uu___3921_29841.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3921_29841.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3921_29841.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3921_29841.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3921_29841.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3921_29841.FStar_TypeChecker_Common.rank)
                       } in
                     solve_c env uu____29838 wl
                 | (FStar_Syntax_Syntax.Comp uu____29846,
                    FStar_Syntax_Syntax.Comp uu____29847) ->
                     let uu____29848 =
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
                     if uu____29848
                     then
                       let uu____29851 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type" in
                       solve_t env uu____29851 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11 in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21 in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29858 =
                            let uu____29863 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name in
                            if uu____29863
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29872 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11 in
                               let uu____29873 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21 in
                               (uu____29872, uu____29873)) in
                          match uu____29858 with
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
                           (let uu____29881 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel") in
                            if uu____29881
                            then
                              let uu____29886 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name in
                              let uu____29888 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29886 uu____29888
                            else ());
                           (let uu____29893 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name in
                            if uu____29893
                            then solve_layered_sub c12 c22
                            else
                              (let uu____29898 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name in
                               match uu____29898 with
                               | FStar_Pervasives_Native.None ->
                                   let uu____29901 =
                                     mklstr
                                       (fun uu____29908 ->
                                          let uu____29909 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name in
                                          let uu____29911 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____29909 uu____29911) in
                                   giveup env uu____29901 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))
let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g ->
    let uu____29922 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm)) in
    FStar_All.pipe_right uu____29922 (FStar_String.concat ", ")
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs ->
    let vars =
      let uu____29972 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string) in
      FStar_All.pipe_right uu____29972 (FStar_String.concat ", ") in
    let ineqs1 =
      let uu____29997 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____30028 ->
                match uu____30028 with
                | (u1, u2) ->
                    let uu____30036 = FStar_Syntax_Print.univ_to_string u1 in
                    let uu____30038 = FStar_Syntax_Print.univ_to_string u2 in
                    FStar_Util.format2 "%s < %s" uu____30036 uu____30038)) in
      FStar_All.pipe_right uu____29997 (FStar_String.concat ", ") in
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
      | (FStar_TypeChecker_Common.Trivial, [], (uu____30075, [])) when
          let uu____30102 = FStar_Options.print_implicits () in
          Prims.op_Negation uu____30102 -> "{}"
      | uu____30105 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____30132 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ()) in
                if uu____30132
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial" in
          let carry defs =
            let uu____30163 =
              FStar_List.map
                (fun uu____30177 ->
                   match uu____30177 with
                   | (msg, x) ->
                       let uu____30188 =
                         let uu____30190 = prob_to_string env x in
                         Prims.op_Hat ": " uu____30190 in
                       Prims.op_Hat msg uu____30188) defs in
            FStar_All.pipe_right uu____30163 (FStar_String.concat ",\n") in
          let imps = print_pending_implicits g in
          let uu____30200 = carry g.FStar_TypeChecker_Common.deferred in
          let uu____30202 = carry g.FStar_TypeChecker_Common.deferred_to_tac in
          let uu____30204 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30200 uu____30202 uu____30204 imps
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
                  let uu____30261 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel")) in
                  if uu____30261
                  then
                    let uu____30269 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs in
                    let uu____30271 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30269
                      (rel_to_string rel) uu____30271
                  else "TOP" in
                let uu____30277 =
                  new_problem wl env lhs rel rhs elt loc reason in
                match uu____30277 with
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
              let uu____30337 =
                let uu____30340 = FStar_TypeChecker_Env.get_range env in
                FStar_All.pipe_left
                  (fun uu____30343 ->
                     FStar_Pervasives_Native.Some uu____30343) uu____30340 in
              FStar_Syntax_Syntax.new_bv uu____30337 t1 in
            let uu____30344 =
              let uu____30349 = FStar_TypeChecker_Env.get_range env in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30349 in
            match uu____30344 with | (p, wl1) -> (p, x, wl1)
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
        (let uu____30421 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench") in
         if uu____30421
         then
           let uu____30426 =
             FStar_Common.string_of_list
               (fun p -> FStar_Util.string_of_int (p_pid p)) probs.attempting in
           FStar_Util.print1 "solving problems %s {\n" uu____30426
         else ());
        (let uu____30433 =
           FStar_Util.record_time (fun uu____30440 -> solve env probs) in
         match uu____30433 with
         | (sol, ms) ->
             ((let uu____30454 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench") in
               if uu____30454
               then
                 let uu____30459 = FStar_Util.string_of_int ms in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30459
               else ());
              (match sol with
               | Success (deferred, defer_to_tac, implicits) ->
                   let uu____30475 =
                     FStar_Util.record_time
                       (fun uu____30482 -> FStar_Syntax_Unionfind.commit tx) in
                   (match uu____30475 with
                    | ((), ms1) ->
                        ((let uu____30495 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench") in
                          if uu____30495
                          then
                            let uu____30500 = FStar_Util.string_of_int ms1 in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30500
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d, s) ->
                   ((let uu____30514 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel")) in
                     if uu____30514
                     then
                       let uu____30521 = explain env d s in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30521
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
          ((let uu____30549 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification") in
            if uu____30549
            then
              let uu____30554 = FStar_Syntax_Print.term_to_string f in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30554
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f in
            (let uu____30562 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification") in
             if uu____30562
             then
               let uu____30567 = FStar_Syntax_Print.term_to_string f1 in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30567
             else ());
            (let f2 =
               let uu____30573 =
                 let uu____30574 = FStar_Syntax_Util.unmeta f1 in
                 uu____30574.FStar_Syntax_Syntax.n in
               match uu____30573 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30578 -> FStar_TypeChecker_Common.NonTrivial f1 in
             let uu___4041_30579 = g in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4041_30579.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4041_30579.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4041_30579.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4041_30579.FStar_TypeChecker_Common.implicits)
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
            let uu____30631 =
              let uu____30632 =
                let uu____30633 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30634 ->
                       FStar_TypeChecker_Common.NonTrivial uu____30634) in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30633;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                } in
              simplify_guard env uu____30632 in
            FStar_All.pipe_left
              (fun uu____30641 -> FStar_Pervasives_Native.Some uu____30641)
              uu____30631
let with_guard_no_simp :
  'uuuuuu30651 .
    'uuuuuu30651 ->
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
            let uu____30700 =
              let uu____30701 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30702 ->
                     FStar_TypeChecker_Common.NonTrivial uu____30702) in
              {
                FStar_TypeChecker_Common.guard_f = uu____30701;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              } in
            FStar_Pervasives_Native.Some uu____30700
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
          (let uu____30735 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____30735
           then
             let uu____30740 = FStar_Syntax_Print.term_to_string t1 in
             let uu____30742 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30740
               uu____30742
           else ());
          (let uu____30747 =
             let uu____30752 = FStar_TypeChecker_Env.get_range env in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30752 in
           match uu____30747 with
           | (prob, wl) ->
               let g =
                 let uu____30760 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30770 -> FStar_Pervasives_Native.None) in
                 FStar_All.pipe_left (with_guard env prob) uu____30760 in
               ((let uu____30792 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel") in
                 if uu____30792
                 then
                   let uu____30797 =
                     FStar_Common.string_of_option (guard_to_string env) g in
                   FStar_Util.print1 "} res = %s\n" uu____30797
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
        let uu____30818 = try_teq true env t1 t2 in
        match uu____30818 with
        | FStar_Pervasives_Native.None ->
            ((let uu____30823 = FStar_TypeChecker_Env.get_range env in
              let uu____30824 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1 in
              FStar_Errors.log_issue uu____30823 uu____30824);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30832 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel") in
              if uu____30832
              then
                let uu____30837 = FStar_Syntax_Print.term_to_string t1 in
                let uu____30839 = FStar_Syntax_Print.term_to_string t2 in
                let uu____30841 = guard_to_string env g in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30837
                  uu____30839 uu____30841
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
        (let uu____30865 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____30865
         then
           let uu____30870 = FStar_Syntax_Print.term_to_string t1 in
           let uu____30872 = FStar_Syntax_Print.term_to_string t2 in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30870
             uu____30872
         else ());
        (let uu____30877 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2 in
         match uu____30877 with
         | (prob, x, wl) ->
             let g =
               let uu____30892 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30903 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____30892 in
             ((let uu____30925 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel") in
               if uu____30925
               then
                 let uu____30930 =
                   FStar_Common.string_of_option (guard_to_string env) g in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30930
               else ());
              (match g with
               | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30938 =
                     let uu____30939 = FStar_Syntax_Syntax.mk_binder x in
                     FStar_TypeChecker_Env.abstract_guard uu____30939 g1 in
                   FStar_Pervasives_Native.Some uu____30938)))
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun e ->
      fun t1 ->
        fun t2 ->
          let uu____30961 = FStar_TypeChecker_Env.get_range env in
          let uu____30962 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1 in
          FStar_Errors.log_issue uu____30961 uu____30962
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
        (let uu____30991 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____30991
         then
           let uu____30996 = FStar_Syntax_Print.comp_to_string c1 in
           let uu____30998 = FStar_Syntax_Print.comp_to_string c2 in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30996 uu____30998
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____31009 =
           let uu____31016 = FStar_TypeChecker_Env.get_range env in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____31016 "sub_comp" in
         match uu____31009 with
         | (prob, wl) ->
             let wl1 =
               let uu___4114_31027 = wl in
               {
                 attempting = (uu___4114_31027.attempting);
                 wl_deferred = (uu___4114_31027.wl_deferred);
                 wl_deferred_to_tac = (uu___4114_31027.wl_deferred_to_tac);
                 ctr = (uu___4114_31027.ctr);
                 defer_ok = (uu___4114_31027.defer_ok);
                 smt_ok = (uu___4114_31027.smt_ok);
                 umax_heuristic_ok = (uu___4114_31027.umax_heuristic_ok);
                 tcenv = (uu___4114_31027.tcenv);
                 wl_implicits = (uu___4114_31027.wl_implicits);
                 repr_subcomp_allowed = true
               } in
             let prob1 = FStar_TypeChecker_Common.CProb prob in
             (def_check_prob "sub_comp" prob1;
              (let uu____31032 =
                 FStar_Util.record_time
                   (fun uu____31044 ->
                      let uu____31045 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____31056 -> FStar_Pervasives_Native.None) in
                      FStar_All.pipe_left (with_guard env prob1) uu____31045) in
               match uu____31032 with
               | (r, ms) ->
                   ((let uu____31088 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench") in
                     if uu____31088
                     then
                       let uu____31093 = FStar_Syntax_Print.comp_to_string c1 in
                       let uu____31095 = FStar_Syntax_Print.comp_to_string c2 in
                       let uu____31097 = FStar_Util.string_of_int ms in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____31093 uu____31095
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____31097
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
      fun uu____31135 ->
        match uu____31135 with
        | (variables, ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31178 =
                 let uu____31184 =
                   let uu____31186 = FStar_Syntax_Print.univ_to_string u1 in
                   let uu____31188 = FStar_Syntax_Print.univ_to_string u2 in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31186 uu____31188 in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31184) in
               let uu____31192 = FStar_TypeChecker_Env.get_range env in
               FStar_Errors.raise_error uu____31178 uu____31192) in
            let equiv v v' =
              let uu____31205 =
                let uu____31210 = FStar_Syntax_Subst.compress_univ v in
                let uu____31211 = FStar_Syntax_Subst.compress_univ v' in
                (uu____31210, uu____31211) in
              match uu____31205 with
              | (FStar_Syntax_Syntax.U_unif v0, FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31235 -> false in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v ->
                      let uu____31266 = FStar_Syntax_Subst.compress_univ v in
                      match uu____31266 with
                      | FStar_Syntax_Syntax.U_unif uu____31273 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31304 ->
                                    match uu____31304 with
                                    | (u, v') ->
                                        let uu____31313 = equiv v v' in
                                        if uu____31313
                                        then
                                          let uu____31318 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u)) in
                                          (if uu____31318 then [] else [u])
                                        else [])) in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v) in
                          [(lb, v)]
                      | uu____31339 -> [])) in
            let uu____31344 =
              let wl =
                let uu___4157_31348 = empty_worklist env in
                {
                  attempting = (uu___4157_31348.attempting);
                  wl_deferred = (uu___4157_31348.wl_deferred);
                  wl_deferred_to_tac = (uu___4157_31348.wl_deferred_to_tac);
                  ctr = (uu___4157_31348.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4157_31348.smt_ok);
                  umax_heuristic_ok = (uu___4157_31348.umax_heuristic_ok);
                  tcenv = (uu___4157_31348.tcenv);
                  wl_implicits = (uu___4157_31348.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4157_31348.repr_subcomp_allowed)
                } in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31367 ->
                      match uu____31367 with
                      | (lb, v) ->
                          let uu____31374 =
                            solve_universe_eq (~- Prims.int_one) wl lb v in
                          (match uu____31374 with
                           | USolved wl1 -> ()
                           | uu____31377 -> fail lb v))) in
            let rec check_ineq uu____31388 =
              match uu____31388 with
              | (u, v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero, uu____31400) -> true
                   | (FStar_Syntax_Syntax.U_succ u0,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name u0,
                      FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif u0,
                      FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name uu____31428,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif uu____31430,
                      FStar_Syntax_Syntax.U_succ v0) -> check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us, uu____31443) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2 -> check_ineq (u2, v1)))
                   | (uu____31451, FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some (fun v2 -> check_ineq (u1, v2)))
                   | uu____31460 -> false) in
            let uu____31466 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31483 ->
                      match uu____31483 with
                      | (u, v) ->
                          let uu____31491 = check_ineq (u, v) in
                          if uu____31491
                          then true
                          else
                            ((let uu____31499 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses") in
                              if uu____31499
                              then
                                let uu____31504 =
                                  FStar_Syntax_Print.univ_to_string u in
                                let uu____31506 =
                                  FStar_Syntax_Print.univ_to_string v in
                                FStar_Util.print2 "%s </= %s" uu____31504
                                  uu____31506
                              else ());
                             false))) in
            if uu____31466
            then ()
            else
              ((let uu____31516 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses") in
                if uu____31516
                then
                  ((let uu____31522 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31522);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31534 = ineqs_to_string (variables, ineqs) in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31534))
                else ());
               (let uu____31547 = FStar_TypeChecker_Env.get_range env in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31547))
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
          let fail uu____31629 =
            match uu____31629 with
            | (d, s) ->
                let msg = explain env d s in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d) in
          let wl =
            let uu___4235_31656 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred in
            {
              attempting = (uu___4235_31656.attempting);
              wl_deferred = (uu___4235_31656.wl_deferred);
              wl_deferred_to_tac = (uu___4235_31656.wl_deferred_to_tac);
              ctr = (uu___4235_31656.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4235_31656.umax_heuristic_ok);
              tcenv = (uu___4235_31656.tcenv);
              wl_implicits = (uu___4235_31656.wl_implicits);
              repr_subcomp_allowed = (uu___4235_31656.repr_subcomp_allowed)
            } in
          (let uu____31659 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel") in
           if uu____31659
           then
             let uu____31664 = FStar_Util.string_of_bool defer_ok in
             let uu____31666 = wl_to_string wl in
             let uu____31668 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits) in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31664 uu____31666 uu____31668
           else ());
          (let g1 =
             let uu____31674 = solve_and_commit env wl fail in
             match uu____31674 with
             | FStar_Pervasives_Native.Some
                 (uu____31683::uu____31684, uu____31685, uu____31686) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred, defer_to_tac, imps) ->
                 let uu___4252_31720 = g in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4252_31720.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4252_31720.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31726 ->
                 failwith "Impossible: should have raised a failure already" in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1 in
            (let uu____31739 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook") in
             if uu____31739
             then
               let uu____31744 = guard_to_string env g2 in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____31744
             else ());
            (let uu___4260_31749 = g2 in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4260_31749.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4260_31749.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4260_31749.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4260_31749.FStar_TypeChecker_Common.implicits)
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
          (let uu____31845 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook") in
           if uu____31845
           then
             let uu____31850 = guard_to_string env g in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31850
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g in
           let ret_g =
             let uu___4277_31857 = g1 in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4277_31857.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4277_31857.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4277_31857.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4277_31857.FStar_TypeChecker_Common.implicits)
             } in
           let uu____31858 =
             let uu____31860 = FStar_TypeChecker_Env.should_verify env in
             Prims.op_Negation uu____31860 in
           if uu____31858
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____31872 = FStar_TypeChecker_Env.get_range env in
                      let uu____31873 =
                        let uu____31875 =
                          FStar_Syntax_Print.term_to_string vc in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31875 in
                      FStar_Errors.diag uu____31872 uu____31873)
                   else ();
                   (let vc1 =
                      let uu____31881 =
                        let uu____31885 =
                          let uu____31887 =
                            FStar_TypeChecker_Env.current_module env in
                          FStar_Ident.string_of_lid uu____31887 in
                        FStar_Pervasives_Native.Some uu____31885 in
                      FStar_Profiling.profile
                        (fun uu____31890 ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31881 "FStar.TypeChecker.Rel.vc_normalization" in
                    if debug
                    then
                      (let uu____31894 = FStar_TypeChecker_Env.get_range env in
                       let uu____31895 =
                         let uu____31897 =
                           FStar_Syntax_Print.term_to_string vc1 in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31897 in
                       FStar_Errors.diag uu____31894 uu____31895)
                    else ();
                    (let uu____31903 = FStar_TypeChecker_Env.get_range env in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31903 "discharge_guard'" env vc1);
                    (let uu____31905 =
                       FStar_TypeChecker_Common.check_trivial vc1 in
                     match uu____31905 with
                     | FStar_TypeChecker_Common.Trivial ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____31914 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____31915 =
                                 let uu____31917 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31917 in
                               FStar_Errors.diag uu____31914 uu____31915)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____31927 =
                                 FStar_TypeChecker_Env.get_range env in
                               let uu____31928 =
                                 let uu____31930 =
                                   FStar_Syntax_Print.term_to_string vc2 in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31930 in
                               FStar_Errors.diag uu____31927 uu____31928)
                            else ();
                            (let vcs =
                               let uu____31944 = FStar_Options.use_tactics () in
                               if uu____31944
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31966 ->
                                      (let uu____31968 =
                                         FStar_Options.set_options
                                           "--no_tactics" in
                                       FStar_All.pipe_left
                                         (fun uu____31970 -> ()) uu____31968);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2 in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____32013 ->
                                               match uu____32013 with
                                               | (env1, goal, opts) ->
                                                   let uu____32029 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal in
                                                   (env1, uu____32029, opts)))))
                               else
                                 (let uu____32033 =
                                    let uu____32040 = FStar_Options.peek () in
                                    (env, vc2, uu____32040) in
                                  [uu____32033]) in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____32073 ->
                                     match uu____32073 with
                                     | (env1, goal, opts) ->
                                         let uu____32083 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal in
                                         (match uu____32083 with
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
                                                 (let uu____32094 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____32095 =
                                                    let uu____32097 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    let uu____32099 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1 in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____32097 uu____32099 in
                                                  FStar_Errors.diag
                                                    uu____32094 uu____32095)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____32106 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1 in
                                                  let uu____32107 =
                                                    let uu____32109 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1 in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____32109 in
                                                  FStar_Errors.diag
                                                    uu____32106 uu____32107)
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
      let uu____32127 =
        discharge_guard' FStar_Pervasives_Native.None env g false in
      match uu____32127 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None ->
          let uu____32136 = FStar_TypeChecker_Env.get_range env in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____32136
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      let uu____32150 =
        discharge_guard' FStar_Pervasives_Native.None env g true in
      match uu____32150 with
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
        let uu____32180 = try_teq false env t1 t2 in
        match uu____32180 with
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
             let uu____32235 =
               ((imp.FStar_TypeChecker_Common.imp_uvar),
                 (imp.FStar_TypeChecker_Common.imp_range)) in
             match uu____32235 with
             | (ctx_u, r) ->
                 let t_norm =
                   FStar_TypeChecker_Normalize.normalize
                     FStar_TypeChecker_Normalize.whnf_steps env
                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                 let uu____32245 =
                   let uu____32246 = FStar_Syntax_Subst.compress t_norm in
                   uu____32246.FStar_Syntax_Syntax.n in
                 (match uu____32245 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.unit_lid
                      ->
                      let uu____32252 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____32252
                        (fun uu____32255 ->
                           FStar_Pervasives_Native.Some uu____32255)
                  | FStar_Syntax_Syntax.Tm_refine (b, uu____32257) when
                      FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                      let uu____32262 =
                        FStar_All.pipe_right r
                          FStar_Syntax_Syntax.unit_const_with_range in
                      FStar_All.pipe_right uu____32262
                        (fun uu____32265 ->
                           FStar_Pervasives_Native.Some uu____32265)
                  | uu____32266 -> FStar_Pervasives_Native.None) in
           let b =
             FStar_List.fold_left
               (fun b ->
                  fun imp ->
                    let uu____32279 =
                      let uu____32281 =
                        FStar_Syntax_Unionfind.find
                          (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
                      FStar_All.pipe_right uu____32281 FStar_Util.is_none in
                    if uu____32279
                    then
                      let uu____32289 = imp_value imp in
                      match uu____32289 with
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
        let uu____32318 =
          if is_tac
          then (false, true)
          else
            (((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
                (Prims.op_Negation env.FStar_TypeChecker_Env.lax)), false) in
        match uu____32318 with
        | (must_total, forcelax) ->
            let rec unresolved ctx_u =
              let uu____32354 =
                FStar_Syntax_Unionfind.find
                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
              match uu____32354 with
              | FStar_Pervasives_Native.Some r ->
                  (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                   | FStar_Pervasives_Native.None -> false
                   | FStar_Pervasives_Native.Some uu____32361 ->
                       let uu____32362 =
                         let uu____32363 = FStar_Syntax_Subst.compress r in
                         uu____32363.FStar_Syntax_Syntax.n in
                       (match uu____32362 with
                        | FStar_Syntax_Syntax.Tm_uvar (ctx_u', uu____32368)
                            -> unresolved ctx_u'
                        | uu____32385 -> false))
              | FStar_Pervasives_Native.None -> true in
            let rec until_fixpoint acc implicits =
              let uu____32409 = acc in
              match uu____32409 with
              | (out, changed) ->
                  (match implicits with
                   | [] ->
                       if Prims.op_Negation changed
                       then
                         let uu____32420 =
                           try_solve_single_valued_implicits env is_tac out in
                         (match uu____32420 with
                          | (out1, changed1) ->
                              if changed1
                              then until_fixpoint ([], false) out1
                              else out1)
                       else until_fixpoint ([], false) out
                   | hd::tl ->
                       let uu____32443 = hd in
                       (match uu____32443 with
                        | { FStar_TypeChecker_Common.imp_reason = reason;
                            FStar_TypeChecker_Common.imp_uvar = ctx_u;
                            FStar_TypeChecker_Common.imp_tm = tm;
                            FStar_TypeChecker_Common.imp_range = r;_} ->
                            if
                              ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                = FStar_Syntax_Syntax.Allow_unresolved
                            then until_fixpoint (out, true) tl
                            else
                              (let uu____32454 = unresolved ctx_u in
                               if uu____32454
                               then
                                 match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                                 with
                                 | FStar_Pervasives_Native.Some
                                     (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                     (env_dyn, tau)) ->
                                     let env1 = FStar_Dyn.undyn env_dyn in
                                     ((let uu____32465 =
                                         FStar_TypeChecker_Env.debug env1
                                           (FStar_Options.Other "Tac") in
                                       if uu____32465
                                       then
                                         let uu____32469 =
                                           FStar_Syntax_Print.ctx_uvar_to_string
                                             ctx_u in
                                         FStar_Util.print1
                                           "Running tactic for meta-arg %s\n"
                                           uu____32469
                                       else ());
                                      (let t =
                                         env1.FStar_TypeChecker_Env.synth_hook
                                           env1
                                           (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                           tau in
                                       let extra =
                                         let uu____32478 =
                                           teq_nosmt env1 t tm in
                                         match uu____32478 with
                                         | FStar_Pervasives_Native.None ->
                                             failwith
                                               "resolve_implicits: unifying with an unresolved uvar failed?"
                                         | FStar_Pervasives_Native.Some g1 ->
                                             g1.FStar_TypeChecker_Common.implicits in
                                       let ctx_u1 =
                                         let uu___4422_32488 = ctx_u in
                                         {
                                           FStar_Syntax_Syntax.ctx_uvar_head
                                             =
                                             (uu___4422_32488.FStar_Syntax_Syntax.ctx_uvar_head);
                                           FStar_Syntax_Syntax.ctx_uvar_gamma
                                             =
                                             (uu___4422_32488.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                           FStar_Syntax_Syntax.ctx_uvar_binders
                                             =
                                             (uu___4422_32488.FStar_Syntax_Syntax.ctx_uvar_binders);
                                           FStar_Syntax_Syntax.ctx_uvar_typ =
                                             (uu___4422_32488.FStar_Syntax_Syntax.ctx_uvar_typ);
                                           FStar_Syntax_Syntax.ctx_uvar_reason
                                             =
                                             (uu___4422_32488.FStar_Syntax_Syntax.ctx_uvar_reason);
                                           FStar_Syntax_Syntax.ctx_uvar_should_check
                                             =
                                             (uu___4422_32488.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                           FStar_Syntax_Syntax.ctx_uvar_range
                                             =
                                             (uu___4422_32488.FStar_Syntax_Syntax.ctx_uvar_range);
                                           FStar_Syntax_Syntax.ctx_uvar_meta
                                             = FStar_Pervasives_Native.None
                                         } in
                                       let hd1 =
                                         let uu___4425_32490 = hd in
                                         {
                                           FStar_TypeChecker_Common.imp_reason
                                             =
                                             (uu___4425_32490.FStar_TypeChecker_Common.imp_reason);
                                           FStar_TypeChecker_Common.imp_uvar
                                             = ctx_u1;
                                           FStar_TypeChecker_Common.imp_tm =
                                             (uu___4425_32490.FStar_TypeChecker_Common.imp_tm);
                                           FStar_TypeChecker_Common.imp_range
                                             =
                                             (uu___4425_32490.FStar_TypeChecker_Common.imp_range)
                                         } in
                                       until_fixpoint (out, true)
                                         (FStar_List.append extra tl)))
                                 | uu____32493 ->
                                     until_fixpoint ((hd :: out), changed) tl
                               else
                                 if
                                   ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                     = FStar_Syntax_Syntax.Allow_untyped
                                 then until_fixpoint (out, true) tl
                                 else
                                   (let env1 =
                                      let uu___4430_32505 = env in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4430_32505.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4430_32505.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4430_32505.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4430_32505.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4430_32505.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4430_32505.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4430_32505.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4430_32505.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4430_32505.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4430_32505.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4430_32505.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4430_32505.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4430_32505.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4430_32505.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4430_32505.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4430_32505.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4430_32505.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4430_32505.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4430_32505.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax =
                                          (uu___4430_32505.FStar_TypeChecker_Env.lax);
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4430_32505.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4430_32505.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4430_32505.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4430_32505.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4430_32505.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4430_32505.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4430_32505.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4430_32505.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4430_32505.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4430_32505.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4430_32505.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4430_32505.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4430_32505.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4430_32505.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4430_32505.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4430_32505.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4430_32505.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4430_32505.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4430_32505.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4430_32505.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4430_32505.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4430_32505.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4430_32505.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4430_32505.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4430_32505.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4430_32505.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      } in
                                    let tm1 =
                                      norm_with_steps
                                        "FStar.TypeChecker.Rel.norm_with_steps.8"
                                        [FStar_TypeChecker_Env.Beta] env1 tm in
                                    let env2 =
                                      if forcelax
                                      then
                                        let uu___4435_32510 = env1 in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___4435_32510.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___4435_32510.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___4435_32510.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___4435_32510.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___4435_32510.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___4435_32510.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___4435_32510.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___4435_32510.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___4435_32510.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___4435_32510.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___4435_32510.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___4435_32510.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___4435_32510.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___4435_32510.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            (uu___4435_32510.FStar_TypeChecker_Env.use_eq);
                                          FStar_TypeChecker_Env.use_eq_strict
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.use_eq_strict);
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___4435_32510.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___4435_32510.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax = true;
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___4435_32510.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___4435_32510.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___4435_32510.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___4435_32510.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___4435_32510.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___4435_32510.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___4435_32510.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___4435_32510.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___4435_32510.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.mpreprocess =
                                            (uu___4435_32510.FStar_TypeChecker_Env.mpreprocess);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___4435_32510.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___4435_32510.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___4435_32510.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___4435_32510.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.erasable_types_tab);
                                          FStar_TypeChecker_Env.enable_defer_to_tac
                                            =
                                            (uu___4435_32510.FStar_TypeChecker_Env.enable_defer_to_tac)
                                        }
                                      else env1 in
                                    (let uu____32515 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env2)
                                         (FStar_Options.Other "Rel") in
                                     if uu____32515
                                     then
                                       let uu____32520 =
                                         FStar_Syntax_Print.uvar_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                       let uu____32522 =
                                         FStar_Syntax_Print.term_to_string
                                           tm1 in
                                       let uu____32524 =
                                         FStar_Syntax_Print.term_to_string
                                           ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                       let uu____32526 =
                                         FStar_Range.string_of_range r in
                                       FStar_Util.print5
                                         "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                         uu____32520 uu____32522 uu____32524
                                         reason uu____32526
                                     else ());
                                    (let g1 =
                                       try
                                         (fun uu___4441_32533 ->
                                            match () with
                                            | () ->
                                                env2.FStar_TypeChecker_Env.check_type_of
                                                  must_total env2 tm1
                                                  ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                           ()
                                       with
                                       | e when FStar_Errors.handleable e ->
                                           ((let uu____32540 =
                                               let uu____32550 =
                                                 let uu____32558 =
                                                   let uu____32560 =
                                                     FStar_Syntax_Print.uvar_to_string
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                                                   let uu____32562 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2 tm1 in
                                                   let uu____32564 =
                                                     FStar_TypeChecker_Normalize.term_to_string
                                                       env2
                                                       ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ in
                                                   FStar_Util.format3
                                                     "Failed while checking implicit %s set to %s of expected type %s"
                                                     uu____32560 uu____32562
                                                     uu____32564 in
                                                 (FStar_Errors.Error_BadImplicit,
                                                   uu____32558, r) in
                                               [uu____32550] in
                                             FStar_Errors.add_errors
                                               uu____32540);
                                            FStar_Exn.raise e) in
                                     let g' =
                                       let uu____32583 =
                                         discharge_guard'
                                           (FStar_Pervasives_Native.Some
                                              (fun uu____32594 ->
                                                 let uu____32595 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tm1 in
                                                 let uu____32597 =
                                                   FStar_Range.string_of_range
                                                     r in
                                                 let uu____32599 =
                                                   FStar_Range.string_of_range
                                                     tm1.FStar_Syntax_Syntax.pos in
                                                 FStar_Util.format4
                                                   "%s (Introduced at %s for %s resolved at %s)"
                                                   uu____32595 uu____32597
                                                   reason uu____32599)) env2
                                           g1 true in
                                       match uu____32583 with
                                       | FStar_Pervasives_Native.Some g2 ->
                                           g2
                                       | FStar_Pervasives_Native.None ->
                                           failwith
                                             "Impossible, with use_smt = true, discharge_guard' should never have returned None" in
                                     until_fixpoint
                                       ((FStar_List.append
                                           g'.FStar_TypeChecker_Common.implicits
                                           out), true) tl))))) in
            let uu___4453_32607 = g in
            let uu____32608 =
              until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4453_32607.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4453_32607.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4453_32607.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs =
                (uu___4453_32607.FStar_TypeChecker_Common.univ_ineqs);
              FStar_TypeChecker_Common.implicits = uu____32608
            }
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env ->
    fun g ->
      (let uu____32623 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____32623
       then
         let uu____32628 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32628
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
      (let uu____32658 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook") in
       if uu____32658
       then
         let uu____32663 = guard_to_string env g in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32663
       else ());
      (let g1 = solve_deferred_constraints env g in
       let g2 = resolve_implicits env g1 in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____32670 = discharge_guard env g2 in
           FStar_All.pipe_left (fun uu____32671 -> ()) uu____32670
       | imp::uu____32673 ->
           let uu____32676 =
             let uu____32682 =
               let uu____32684 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
               let uu____32686 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____32684 uu____32686
                 imp.FStar_TypeChecker_Common.imp_reason in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32682) in
           FStar_Errors.raise_error uu____32676
             imp.FStar_TypeChecker_Common.imp_range)
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32706 = teq env t1 t2 in
        force_trivial_guard env uu____32706
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32725 = teq_nosmt env t1 t2 in
        match uu____32725 with
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
          (let uu____32761 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns") in
           if uu____32761
           then
             let uu____32766 =
               let uu____32768 =
                 FStar_All.pipe_right reason FStar_Util.is_none in
               if uu____32768
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must in
             let uu____32785 = FStar_Syntax_Print.term_to_string t1 in
             let uu____32787 = FStar_Syntax_Print.term_to_string t2 in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____32766
               uu____32785 uu____32787
           else ());
          teq env t1 t2
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1 ->
    fun u2 ->
      let uu___4491_32803 = FStar_TypeChecker_Common.trivial_guard in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4491_32803.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4491_32803.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4491_32803.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4491_32803.FStar_TypeChecker_Common.implicits)
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
        (let uu____32839 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____32839
         then
           let uu____32844 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____32846 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32844
             uu____32846
         else ());
        (let uu____32851 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____32851 with
         | (prob, x, wl) ->
             let g =
               let uu____32870 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32881 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____32870 in
             ((let uu____32903 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g) in
               if uu____32903
               then
                 let uu____32908 =
                   FStar_TypeChecker_Normalize.term_to_string env t1 in
                 let uu____32910 =
                   FStar_TypeChecker_Normalize.term_to_string env t2 in
                 let uu____32912 =
                   let uu____32914 = FStar_Util.must g in
                   guard_to_string env uu____32914 in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32908 uu____32910 uu____32912
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
        let uu____32951 = check_subtyping env t1 t2 in
        match uu____32951 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____32970 =
              let uu____32971 = FStar_Syntax_Syntax.mk_binder x in
              FStar_TypeChecker_Env.abstract_guard uu____32971 g in
            FStar_Pervasives_Native.Some uu____32970
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____32990 = check_subtyping env t1 t2 in
        match uu____32990 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x, g) ->
            let uu____33009 =
              let uu____33010 =
                let uu____33011 = FStar_Syntax_Syntax.mk_binder x in
                [uu____33011] in
              FStar_TypeChecker_Env.close_guard env uu____33010 g in
            FStar_Pervasives_Native.Some uu____33009
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        (let uu____33049 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel") in
         if uu____33049
         then
           let uu____33054 =
             FStar_TypeChecker_Normalize.term_to_string env t1 in
           let uu____33056 =
             FStar_TypeChecker_Normalize.term_to_string env t2 in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____33054
             uu____33056
         else ());
        (let uu____33061 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2 in
         match uu____33061 with
         | (prob, x, wl) ->
             let g =
               let uu____33076 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____33087 -> FStar_Pervasives_Native.None) in
               FStar_All.pipe_left (with_guard env prob) uu____33076 in
             (match g with
              | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____33112 =
                      let uu____33113 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____33113] in
                    FStar_TypeChecker_Env.close_guard env uu____33112 g1 in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        let uu____33154 = subtype_nosmt env t1 t2 in
        match uu____33154 with
        | FStar_Pervasives_Native.None -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)