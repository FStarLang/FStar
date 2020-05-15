open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
let (mklstr : (unit -> Prims.string) -> Prims.string FStar_Thunk.thunk) =
  fun f  ->
    let uf = FStar_Syntax_Unionfind.get ()  in
    FStar_Thunk.mk
      (fun uu____43  ->
         let tx = FStar_Syntax_Unionfind.new_transaction ()  in
         FStar_Syntax_Unionfind.set uf;
         (let r = f ()  in FStar_Syntax_Unionfind.rollback tx; r))
  
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____81 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____116 -> false
  
let (__proj__UNIV__item___0 :
  uvi -> (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe))
  = fun projectee  -> match projectee with | UNIV _0 -> _0 
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
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        wl_deferred
  
let (__proj__Mkworklist__item__wl_deferred_to_tac :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        wl_deferred_to_tac
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Common.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        wl_implicits
  
let (__proj__Mkworklist__item__repr_subcomp_allowed : worklist -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits; repr_subcomp_allowed;_} ->
        repr_subcomp_allowed
  
let (as_deferred :
  (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ->
    FStar_TypeChecker_Common.deferred)
  =
  fun wl_def  ->
    FStar_List.map
      (fun uu____780  ->
         match uu____780 with
         | (uu____796,m,p) ->
             let uu____807 = FStar_Thunk.force m  in (uu____807, p)) wl_def
  
let (as_wl_deferred :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun wl  ->
    fun d  ->
      FStar_List.map
        (fun uu____859  ->
           match uu____859 with
           | (m,p) ->
               let uu____879 = FStar_Thunk.mkv m  in ((wl.ctr), uu____879, p))
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
  fun reason  ->
    fun wl  ->
      fun r  ->
        fun gamma  ->
          fun binders  ->
            fun k  ->
              fun should_check  ->
                fun meta  ->
                  let ctx_uvar =
                    let uu____972 = FStar_Syntax_Unionfind.fresh r  in
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
                    }  in
                  FStar_TypeChecker_Common.check_uvar_ctx_invariant reason r
                    true gamma binders;
                  (let t =
                     FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_uvar
                          (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange))) r
                      in
                   let imp =
                     {
                       FStar_TypeChecker_Common.imp_reason = reason;
                       FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Common.imp_tm = t;
                       FStar_TypeChecker_Common.imp_range = r
                     }  in
                   (let uu____1006 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____1006
                    then
                      let uu____1010 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____1010
                    else ());
                   (ctx_uvar, t,
                     ((let uu___94_1016 = wl  in
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
  fun u  ->
    fun bs  ->
      fun t  ->
        fun wl  ->
          let env =
            let uu___100_1049 = wl.tcenv  in
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
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____1051 = FStar_TypeChecker_Env.all_binders env1  in
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
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____1142 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred *
      FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1183 -> false
  
let (__proj__Failed__item___0 :
  solution -> (FStar_TypeChecker_Common.prob * lstring)) =
  fun projectee  -> match projectee with | Failed _0 -> _0 
let (extend_wl :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      FStar_TypeChecker_Common.implicits -> worklist)
  =
  fun wl  ->
    fun defer_to_tac  ->
      fun imps  ->
        let uu___109_1220 = wl  in
        let uu____1221 =
          let uu____1231 = as_wl_deferred wl defer_to_tac  in
          FStar_List.append wl.wl_deferred_to_tac uu____1231  in
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
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____1257 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1268 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1279 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_1297  ->
    match uu___0_1297 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1309 = FStar_Syntax_Util.head_and_args t  in
    match uu____1309 with
    | (head,args) ->
        (match head.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1372 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1374 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1389 =
                     let uu____1391 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1391  in
                   FStar_Util.format1 "@<%s>" uu____1389
                in
             let uu____1395 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1372 uu____1374 uu____1395
         | uu____1398 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_1410  ->
      match uu___1_1410 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1415 =
            let uu____1419 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1421 =
              let uu____1425 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1427 =
                let uu____1431 =
                  let uu____1435 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1435]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1431
                 in
              uu____1425 :: uu____1427  in
            uu____1419 :: uu____1421  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1415
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1446 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1448 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1450 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1446 uu____1448
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1450
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_1464  ->
      match uu___2_1464 with
      | UNIV (u,t) ->
          let x =
            let uu____1470 = FStar_Options.hide_uvar_nums ()  in
            if uu____1470
            then "?"
            else
              (let uu____1477 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1477 FStar_Util.string_of_int)
             in
          let uu____1481 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s <- %s" x uu____1481
      | TERM (u,t) ->
          let x =
            let uu____1488 = FStar_Options.hide_uvar_nums ()  in
            if uu____1488
            then "?"
            else
              (let uu____1495 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1495 FStar_Util.string_of_int)
             in
          let uu____1499 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s <- %s" x uu____1499
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  -> FStar_Common.string_of_list (uvi_to_string env) uvis
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1529 =
      let uu____1533 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1533
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1529 (FStar_String.concat ", ")
  
let args_to_string :
  'uuuuuu1552 .
    (FStar_Syntax_Syntax.term * 'uuuuuu1552) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1571 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1592  ->
              match uu____1592 with
              | (x,uu____1599) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1571 (FStar_String.concat " ")
  
let (empty_worklist : FStar_TypeChecker_Env.env -> worklist) =
  fun env  ->
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
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1647 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1647
         then
           let uu____1652 = FStar_Thunk.force reason  in
           let uu____1655 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1652 uu____1655
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1678 = mklstr (fun uu____1681  -> reason)  in
        giveup env uu____1678 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1687  ->
    match uu___3_1687 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'uuuuuu1693 .
    'uuuuuu1693 FStar_TypeChecker_Common.problem ->
      'uuuuuu1693 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___169_1705 = p  in
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
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1733  ->
    match uu___4_1733 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1739  -> FStar_TypeChecker_Common.TProb uu____1739)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun uu____1745  -> FStar_TypeChecker_Common.CProb uu____1745)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1751  ->
    match uu___5_1751 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___181_1757 = p  in
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
          (let uu___185_1765 = p  in
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
  fun rel  ->
    fun uu___6_1778  ->
      match uu___6_1778 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1785  ->
    match uu___7_1785 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1798  ->
    match uu___8_1798 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1813  ->
    match uu___9_1813 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1828  ->
    match uu___10_1828 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1842  ->
    match uu___11_1842 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1856  ->
    match uu___12_1856 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1868  ->
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
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1914 =
          let uu____1916 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1916  in
        if uu____1914
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1953)::bs ->
                 (FStar_TypeChecker_Env.def_check_closed_in rng msg prev
                    bv.FStar_Syntax_Syntax.sort;
                  aux (FStar_List.append prev [bv]) bs)
              in
           aux [] r)
  
let (p_scope :
  FStar_TypeChecker_Common.prob ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun prob  ->
    let r =
      match prob with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____2000 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____2024 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____2024]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____2000
      | FStar_TypeChecker_Common.CProb p ->
          let uu____2052 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____2076 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____2076]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____2052
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____2123 =
          let uu____2125 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2125  in
        if uu____2123
        then ()
        else
          (let uu____2130 =
             let uu____2133 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____2133
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____2130 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____2182 =
          let uu____2184 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2184  in
        if uu____2182
        then ()
        else
          (let uu____2189 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____2189)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____2209 =
        let uu____2211 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____2211  in
      if uu____2209
      then ()
      else
        (let msgf m =
           let uu____2225 =
             let uu____2227 =
               let uu____2229 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____2229 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____2227  in
           Prims.op_Hat msg uu____2225  in
         (let uu____2234 = msgf "scope"  in
          let uu____2237 = p_scope prob  in
          def_scope_wf uu____2234 (p_loc prob) uu____2237);
         (let uu____2249 = msgf "guard"  in
          def_check_scoped uu____2249 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____2256 = msgf "lhs"  in
                def_check_scoped uu____2256 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2259 = msgf "rhs"  in
                def_check_scoped uu____2259 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____2266 = msgf "lhs"  in
                def_check_scoped_comp uu____2266 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2269 = msgf "rhs"  in
                def_check_scoped_comp uu____2269 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___278_2290 = wl  in
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
  fun env  ->
    fun g  ->
      let uu___282_2321 = empty_worklist env  in
      let uu____2322 = FStar_List.map FStar_Pervasives_Native.snd g  in
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
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___287_2343 = wl  in
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
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____2370 = FStar_Thunk.mkv reason  in defer uu____2370 prob wl
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___295_2389 = wl  in
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
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____2437 = FStar_Syntax_Util.type_u ()  in
            match uu____2437 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____2449 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____2449 with
                 | (uu____2461,tt,wl1) ->
                     let uu____2464 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2464, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2470  ->
    match uu___14_2470 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun uu____2476  -> FStar_TypeChecker_Common.TProb uu____2476)
          (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun uu____2482  -> FStar_TypeChecker_Common.CProb uu____2482)
          (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2490 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2490 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2510  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
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
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  let scope1 =
                    match elt with
                    | FStar_Pervasives_Native.None  -> scope
                    | FStar_Pervasives_Native.Some x ->
                        let uu____2639 =
                          let uu____2648 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2648]  in
                        FStar_List.append scope uu____2639
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2691 =
                      let uu____2694 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2694  in
                    FStar_List.append uu____2691
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2713 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2713 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2733 = next_pid ()  in
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
                        }  in
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
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.op_Hat reason ".mk_t.arg") orig;
                  (let uu____2807 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2807 with
                   | (p,wl1) ->
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
  fun wl  ->
    fun scope  ->
      fun orig  ->
        fun lhs  ->
          fun rel  ->
            fun rhs  ->
              fun elt  ->
                fun reason  ->
                  def_check_prob (Prims.op_Hat reason ".mk_c.arg") orig;
                  (let uu____2895 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2895 with
                   | (p,wl1) ->
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
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun subject  ->
              fun loc  ->
                fun reason  ->
                  let lg_ty =
                    match subject with
                    | FStar_Pervasives_Native.None  ->
                        FStar_Syntax_Util.ktype0
                    | FStar_Pervasives_Native.Some x ->
                        let bs =
                          let uu____3001 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3001]  in
                        let uu____3020 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____3020
                     in
                  let uu____3023 =
                    let uu____3030 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___378_3041 = wl  in
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
                      FStar_Pervasives_Native.None
                     in
                  match uu____3023 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____3053 =
                              let uu____3054 =
                                let uu____3063 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.as_arg uu____3063
                                 in
                              [uu____3054]  in
                            FStar_Syntax_Syntax.mk_Tm_app lg uu____3053 loc
                         in
                      let prob =
                        let uu____3091 = next_pid ()  in
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
                        }  in
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
  fun orig  ->
    fun lhs  ->
      fun rel  ->
        fun rhs  ->
          fun elt  ->
            fun reason  ->
              let p =
                let uu____3139 = next_pid ()  in
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
                }  in
              def_check_prob reason (FStar_TypeChecker_Common.TProb p); p
  
let guard_on_element :
  'uuuuuu3154 .
    worklist ->
      'uuuuuu3154 FStar_TypeChecker_Common.problem ->
        FStar_Syntax_Syntax.bv ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun wl  ->
    fun problem  ->
      fun x  ->
        fun phi  ->
          match problem.FStar_TypeChecker_Common.element with
          | FStar_Pervasives_Native.None  ->
              let u =
                (wl.tcenv).FStar_TypeChecker_Env.universe_of wl.tcenv
                  x.FStar_Syntax_Syntax.sort
                 in
              FStar_Syntax_Util.mk_forall u x phi
          | FStar_Pervasives_Native.Some e ->
              let uu____3187 =
                let uu____3190 =
                  let uu____3191 =
                    let uu____3198 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____3198)  in
                  FStar_Syntax_Syntax.NT uu____3191  in
                [uu____3190]  in
              FStar_Syntax_Subst.subst uu____3187 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____3220 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____3220
        then
          let uu____3228 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____3231 = prob_to_string env d  in
          let uu____3233 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____3240 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3228 uu____3231 uu____3233 uu____3240
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____3252 -> failwith "impossible"  in
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
                   cp.FStar_TypeChecker_Common.rhs
              in
           match uu____3255 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3298  ->
            match uu___15_3298 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3312 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____3316 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3316 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_3347  ->
           match uu___16_3347 with
           | UNIV uu____3350 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____3357 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____3357
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None)
  
let (find_univ_uvar :
  FStar_Syntax_Syntax.universe_uvar ->
    uvi Prims.list ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun u  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___17_3385  ->
           match uu___17_3385 with
           | UNIV (u',t) ->
               let uu____3390 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____3390
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3397 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3409 =
        let uu____3410 =
          let uu____3411 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3411
           in
        FStar_Syntax_Subst.compress uu____3410  in
      FStar_All.pipe_right uu____3409 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3423 =
        let uu____3424 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3424  in
      FStar_All.pipe_right uu____3423 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3436 =
        let uu____3440 =
          let uu____3442 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3442  in
        FStar_Pervasives_Native.Some uu____3440  in
      FStar_Profiling.profile (fun uu____3445  -> sn' env t) uu____3436
        "FStar.TypeChecker.Rel.sn"
  
let (norm_with_steps :
  Prims.string ->
    FStar_TypeChecker_Env.steps ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun profiling_tag  ->
    fun steps  ->
      fun env  ->
        fun t  ->
          let uu____3470 =
            let uu____3474 =
              let uu____3476 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3476  in
            FStar_Pervasives_Native.Some uu____3474  in
          FStar_Profiling.profile
            (fun uu____3479  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3470
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3487 = FStar_Syntax_Util.head_and_args t  in
    match uu____3487 with
    | (h,uu____3506) ->
        let uu____3531 =
          let uu____3532 = FStar_Syntax_Subst.compress h  in
          uu____3532.FStar_Syntax_Syntax.n  in
        (match uu____3531 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3537 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3550 =
        let uu____3554 =
          let uu____3556 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3556  in
        FStar_Pervasives_Native.Some uu____3554  in
      FStar_Profiling.profile
        (fun uu____3561  ->
           let uu____3562 = should_strongly_reduce t  in
           if uu____3562
           then
             let uu____3565 =
               let uu____3566 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3566  in
             FStar_All.pipe_right uu____3565 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3550 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'uuuuuu3577 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu3577) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu3577)
  =
  fun env  ->
    fun t  ->
      let uu____3600 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3600, (FStar_Pervasives_Native.snd t))
  
let (sn_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env  ->
    fun binders  ->
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun uu____3652  ->
              match uu____3652 with
              | (x,imp) ->
                  let uu____3671 =
                    let uu___484_3672 = x  in
                    let uu____3673 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___484_3672.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___484_3672.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3673
                    }  in
                  (uu____3671, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3697 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3697
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3701 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3701
        | uu____3704 -> u2  in
      let uu____3705 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3705
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3722 =
          let uu____3726 =
            let uu____3728 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3728  in
          FStar_Pervasives_Native.Some uu____3726  in
        FStar_Profiling.profile
          (fun uu____3731  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3722 "FStar.TypeChecker.Rel.normalize_refinement"
  
let (base_and_refinement_maybe_delta :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  =
  fun should_delta  ->
    fun env  ->
      fun t1  ->
        let norm_refinement env1 t =
          let steps =
            if should_delta
            then
              [FStar_TypeChecker_Env.Weak;
              FStar_TypeChecker_Env.HNF;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant]
            else [FStar_TypeChecker_Env.Weak; FStar_TypeChecker_Env.HNF]  in
          normalize_refinement steps env1 t  in
        let rec aux norm t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3853 = norm_refinement env t12  in
                 match uu____3853 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3868;
                     FStar_Syntax_Syntax.vars = uu____3869;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3893 =
                       let uu____3895 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3897 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3895 uu____3897
                        in
                     failwith uu____3893)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3913 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm uu____3913
          | FStar_Syntax_Syntax.Tm_uinst uu____3914 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3951 =
                   let uu____3952 = FStar_Syntax_Subst.compress t1'  in
                   uu____3952.FStar_Syntax_Syntax.n  in
                 match uu____3951 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3967 -> aux true t1'
                 | uu____3975 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3990 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4021 =
                   let uu____4022 = FStar_Syntax_Subst.compress t1'  in
                   uu____4022.FStar_Syntax_Syntax.n  in
                 match uu____4021 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4037 -> aux true t1'
                 | uu____4045 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4060 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4107 =
                   let uu____4108 = FStar_Syntax_Subst.compress t1'  in
                   uu____4108.FStar_Syntax_Syntax.n  in
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
                let uu____4390 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4392 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4390 uu____4392
                 in
              failwith uu____4388
          | FStar_Syntax_Syntax.Tm_ascribed uu____4407 ->
              let uu____4434 =
                let uu____4436 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4438 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4436 uu____4438
                 in
              failwith uu____4434
          | FStar_Syntax_Syntax.Tm_delayed uu____4453 ->
              let uu____4468 =
                let uu____4470 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4472 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4470 uu____4472
                 in
              failwith uu____4468
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4487 =
                let uu____4489 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4491 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4489 uu____4491
                 in
              failwith uu____4487
           in
        let uu____4506 = whnf env t1  in aux false uu____4506
  
let (base_and_refinement :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option))
  = fun env  -> fun t  -> base_and_refinement_maybe_delta false env t 
let (unrefine :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun t  ->
      let uu____4551 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4551 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4592 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4592, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta  ->
    fun env  ->
      fun t  ->
        let uu____4619 = base_and_refinement_maybe_delta delta env t  in
        match uu____4619 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4679  ->
    match uu____4679 with
    | (t_base,refopt) ->
        let uu____4710 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4710 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4752 =
      let uu____4756 =
        let uu____4759 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4784  ->
                  match uu____4784 with | (uu____4792,uu____4793,x) -> x))
           in
        FStar_List.append wl.attempting uu____4759  in
      FStar_List.map (wl_prob_to_string wl) uu____4756  in
    FStar_All.pipe_right uu____4752 (FStar_String.concat "\n\t")
  
type flex_t =
  | Flex of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
  FStar_Syntax_Syntax.args) 
let (uu___is_Flex : flex_t -> Prims.bool) = fun projectee  -> true 
let (__proj__Flex__item___0 :
  flex_t ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar *
      FStar_Syntax_Syntax.args))
  = fun projectee  -> match projectee with | Flex _0 -> _0 
let (flex_reason : flex_t -> Prims.string) =
  fun uu____4853  ->
    match uu____4853 with
    | Flex (uu____4855,u,uu____4857) -> u.FStar_Syntax_Syntax.ctx_uvar_reason
  
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4864  ->
    match uu____4864 with
    | Flex (uu____4866,c,args) ->
        let uu____4869 = print_ctx_uvar c  in
        let uu____4871 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4869 uu____4871
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4881 = FStar_Syntax_Util.head_and_args t  in
    match uu____4881 with
    | (head,_args) ->
        let uu____4925 =
          let uu____4926 = FStar_Syntax_Subst.compress head  in
          uu____4926.FStar_Syntax_Syntax.n  in
        (match uu____4925 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4930 -> true
         | uu____4944 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4952 = FStar_Syntax_Util.head_and_args t  in
    match uu____4952 with
    | (head,_args) ->
        let uu____4995 =
          let uu____4996 = FStar_Syntax_Subst.compress head  in
          uu____4996.FStar_Syntax_Syntax.n  in
        (match uu____4995 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____5000) -> u
         | uu____5017 -> failwith "Not a flex-uvar")
  
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0  ->
    fun wl  ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x  in
        let t_x' = FStar_Syntax_Subst.subst' s t_x  in
        let uu____5053 =
          let uu____5054 = FStar_Syntax_Subst.compress t_x'  in
          uu____5054.FStar_Syntax_Syntax.n  in
        match uu____5053 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____5059 -> false  in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____5075 -> true  in
      let uu____5077 = FStar_Syntax_Util.head_and_args t0  in
      match uu____5077 with
      | (head,args) ->
          let uu____5124 =
            let uu____5125 = FStar_Syntax_Subst.compress head  in
            uu____5125.FStar_Syntax_Syntax.n  in
          (match uu____5124 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____5133)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5149) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____5190 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               (match uu____5190 with
                | (gamma_aff,new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____5217 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff
                            in
                         let uu____5221 =
                           let uu____5228 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma
                              in
                           let uu____5237 =
                             let uu____5240 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             FStar_Syntax_Util.arrow dom_binders uu____5240
                              in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____5228
                             uu____5237
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta
                            in
                         (match uu____5221 with
                          | (v,t_v,wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____5276  ->
                                     match uu____5276 with
                                     | (x,i) ->
                                         let uu____5295 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____5295, i)) dom_binders
                                 in
                              let sol =
                                FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                  t0.FStar_Syntax_Syntax.pos
                                 in
                              (FStar_Syntax_Util.set_uvar
                                 uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                               (let args_sol_s =
                                  FStar_List.map
                                    (fun uu____5325  ->
                                       match uu____5325 with
                                       | (a,i) ->
                                           let uu____5344 =
                                             FStar_Syntax_Subst.subst' s a
                                              in
                                           (uu____5344, i)) args_sol
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    t0.FStar_Syntax_Syntax.pos
                                   in
                                (t, wl1))))))
           | uu____5354 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
  
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t  ->
    let uu____5366 = FStar_Syntax_Util.head_and_args t  in
    match uu____5366 with
    | (head,args) ->
        let uu____5409 =
          let uu____5410 = FStar_Syntax_Subst.compress head  in
          uu____5410.FStar_Syntax_Syntax.n  in
        (match uu____5409 with
         | FStar_Syntax_Syntax.Tm_uvar (uv,s) -> Flex (t, uv, args)
         | uu____5431 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t  ->
    fun wl  ->
      let uu____5452 = ensure_no_uvar_subst t wl  in
      match uu____5452 with
      | (t1,wl1) ->
          let uu____5463 = destruct_flex_t' t1  in (uu____5463, wl1)
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5480 =
          let uu____5503 =
            let uu____5504 = FStar_Syntax_Subst.compress k  in
            uu____5504.FStar_Syntax_Syntax.n  in
          match uu____5503 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5586 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5586)
              else
                (let uu____5621 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5621 with
                 | (ys',t1,uu____5654) ->
                     let uu____5659 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5659))
          | uu____5698 ->
              let uu____5699 =
                let uu____5704 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5704)  in
              ((ys, t), uu____5699)
           in
        match uu____5480 with
        | ((ys1,t1),(xs,c)) ->
            if (FStar_List.length xs) <> (FStar_List.length ys1)
            then
              FStar_Syntax_Util.abs ys1 t1
                (FStar_Pervasives_Native.Some
                   (FStar_Syntax_Util.mk_residual_comp
                      FStar_Parser_Const.effect_Tot_lid
                      FStar_Pervasives_Native.None []))
            else
              (let c1 =
                 let uu____5799 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5799 c  in
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
  fun resolve_ok  ->
    fun prob  ->
      fun logical_guard  ->
        fun uvis  ->
          fun wl  ->
            def_check_prob "solve_prob'" prob;
            (let phi =
               match logical_guard with
               | FStar_Pervasives_Native.None  -> FStar_Syntax_Util.t_true
               | FStar_Pervasives_Native.Some phi -> phi  in
             let assign_solution xs uv phi1 =
               (let uu____5877 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5877
                then
                  let uu____5882 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5884 = print_ctx_uvar uv  in
                  let uu____5886 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5882 uu____5884 uu____5886
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5895 =
                   let uu____5897 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5897  in
                 let uu____5900 =
                   let uu____5903 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5903
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5895 uu____5900 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail uu____5936 =
               let uu____5937 =
                 let uu____5939 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5941 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5939 uu____5941
                  in
               failwith uu____5937  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____6007  ->
                       match uu____6007 with
                       | (a,i) ->
                           let uu____6028 =
                             let uu____6029 = FStar_Syntax_Subst.compress a
                                in
                             uu____6029.FStar_Syntax_Syntax.n  in
                           (match uu____6028 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____6055 -> (fail (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____6065 =
                 let uu____6067 = is_flex g  in Prims.op_Negation uu____6067
                  in
               if uu____6065
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____6076 = destruct_flex_t g wl  in
                  match uu____6076 with
                  | (Flex (uu____6081,uv1,args),wl1) ->
                      ((let uu____6086 = args_as_binders args  in
                        assign_solution uu____6086 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___762_6088 = wl1  in
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
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____6113 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____6113
         then
           let uu____6118 = FStar_Util.string_of_int pid  in
           let uu____6120 = uvis_to_string wl.tcenv sol  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6118 uu____6120
         else ());
        commit sol;
        (let uu___770_6126 = wl  in
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
  fun prob  ->
    fun logical_guard  ->
      fun uvis  ->
        fun wl  ->
          def_check_prob "solve_prob.prob" prob;
          FStar_Util.iter_opt logical_guard
            (def_check_scoped "solve_prob.guard" prob);
          (let uu____6162 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____6162
           then
             let uu____6167 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____6171 = uvis_to_string wl.tcenv uvis  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6167 uu____6171
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars =
        let uu____6198 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____6198 FStar_Util.set_elements  in
      let occurs =
        FStar_All.pipe_right uvars
          (FStar_Util.for_some
             (fun uv  ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head))
         in
      (uvars, occurs)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string
        FStar_Pervasives_Native.option))
  =
  fun uk  ->
    fun t  ->
      let uu____6238 = occurs uk t  in
      match uu____6238 with
      | (uvars,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6277 =
                 let uu____6279 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____6281 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6279 uu____6281
                  in
               FStar_Pervasives_Native.Some uu____6277)
             in
          (uvars, (Prims.op_Negation occurs1), msg)
  
let rec (maximal_prefix :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * (FStar_Syntax_Syntax.binders *
        FStar_Syntax_Syntax.binders)))
  =
  fun bs  ->
    fun bs'  ->
      match (bs, bs') with
      | ((b,i)::bs_tail,(b',i')::bs'_tail) ->
          let uu____6392 = FStar_Syntax_Syntax.bv_eq b b'  in
          if uu____6392
          then
            let uu____6403 = maximal_prefix bs_tail bs'_tail  in
            (match uu____6403 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6454 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6511  ->
             match uu____6511 with
             | (x,uu____6523) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6541 = FStar_List.last bs  in
      match uu____6541 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6565) ->
          let uu____6576 =
            FStar_Util.prefix_until
              (fun uu___18_6591  ->
                 match uu___18_6591 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6594 -> false) g
             in
          (match uu____6576 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6608,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6645 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6645 with
        | (pfx,uu____6655) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6667 =
              let uu____6674 =
                let uu____6676 =
                  FStar_Syntax_Print.uvar_to_string
                    src.FStar_Syntax_Syntax.ctx_uvar_head
                   in
                Prims.op_Hat "restricted " uu____6676  in
              new_uvar uu____6674 wl src.FStar_Syntax_Syntax.ctx_uvar_range g
                pfx src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6667 with
             | (uu____6679,src',wl1) ->
                 (FStar_Syntax_Util.set_uvar
                    src.FStar_Syntax_Syntax.ctx_uvar_head src';
                  wl1))
  
let (restrict_all_uvars :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar Prims.list -> worklist -> worklist)
  =
  fun tgt  ->
    fun sources  ->
      fun wl  -> FStar_List.fold_right (restrict_ctx tgt) sources wl
  
let (intersect_binders :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun g  ->
    fun v1  ->
      fun v2  ->
        let as_set v =
          FStar_All.pipe_right v
            (FStar_List.fold_left
               (fun out  ->
                  fun x  ->
                    FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
               FStar_Syntax_Syntax.no_names)
           in
        let v1_set = as_set v1  in
        let ctx_binders =
          FStar_List.fold_left
            (fun out  ->
               fun b  ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____6793 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6794 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6858  ->
                  fun uu____6859  ->
                    match (uu____6858, uu____6859) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6962 =
                          let uu____6964 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6964
                           in
                        if uu____6962
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6998 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6998
                           then
                             let uu____7015 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____7015)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6794 with | (isect,uu____7065) -> FStar_List.rev isect
  
let binders_eq :
  'uuuuuu7101 'uuuuuu7102 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu7101) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7102) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7160  ->
              fun uu____7161  ->
                match (uu____7160, uu____7161) with
                | ((a,uu____7180),(b,uu____7182)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'uuuuuu7198 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7198) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____7229  ->
           match uu____7229 with
           | (y,uu____7236) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'uuuuuu7246 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7246) Prims.list ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) Prims.list ->
          FStar_Syntax_Syntax.binders FStar_Pervasives_Native.option
  =
  fun env  ->
    fun ctx  ->
      fun args  ->
        let rec aux seen args1 =
          match args1 with
          | [] -> FStar_Pervasives_Native.Some (FStar_List.rev seen)
          | (arg,i)::args2 ->
              let hd = sn env arg  in
              (match hd.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____7408 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____7408
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7441 -> FStar_Pervasives_Native.None)
           in
        aux [] args
  
type match_result =
  | MisMatch of (FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option * FStar_Syntax_Syntax.delta_depth
  FStar_Pervasives_Native.option) 
  | HeadMatch of Prims.bool 
  | FullMatch 
let (uu___is_MisMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | MisMatch _0 -> true | uu____7493 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7537 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7558 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7566  ->
    match uu___19_7566 with
    | MisMatch (d1,d2) ->
        let uu____7578 =
          let uu____7580 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7582 =
            let uu____7584 =
              let uu____7586 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7586 ")"  in
            Prims.op_Hat ") (" uu____7584  in
          Prims.op_Hat uu____7580 uu____7582  in
        Prims.op_Hat "MisMatch (" uu____7578
    | HeadMatch u ->
        let uu____7593 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7593
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___20_7602  ->
    match uu___20_7602 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7619 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7634 =
            (let uu____7640 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                in
             let uu____7642 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             uu____7640 = uu____7642) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
             in
          if uu____7634 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7651 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7651 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7662 -> d)
      | d1 -> d1
  
let rec (delta_depth_of_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta uu____7686 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7696 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7715 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7715
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7716 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7717 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7718 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7731 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7745 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7769) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7775,uu____7776) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7818) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7843;
             FStar_Syntax_Syntax.index = uu____7844;
             FStar_Syntax_Syntax.sort = t2;_},uu____7846)
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
          let uu____7898 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7898
  
let rec (head_matches :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> match_result)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let t11 = FStar_Syntax_Util.unmeta t1  in
        let t21 = FStar_Syntax_Util.unmeta t2  in
        match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
        | (FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7917;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7918;
             FStar_Syntax_Syntax.ltyp = uu____7919;
             FStar_Syntax_Syntax.rng = uu____7920;_},uu____7921)
            ->
            let uu____7932 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7932 t21
        | (uu____7933,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7934;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7935;
             FStar_Syntax_Syntax.ltyp = uu____7936;
             FStar_Syntax_Syntax.rng = uu____7937;_})
            ->
            let uu____7948 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7948
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7951 = FStar_Syntax_Syntax.bv_eq x y  in
            if uu____7951
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7962 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7962
            then FullMatch
            else
              (let uu____7967 =
                 let uu____7976 =
                   let uu____7979 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7979  in
                 let uu____7980 =
                   let uu____7983 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7983  in
                 (uu____7976, uu____7980)  in
               MisMatch uu____7967)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7989),FStar_Syntax_Syntax.Tm_uinst (g,uu____7991)) ->
            let uu____8000 = head_matches env f g  in
            FStar_All.pipe_right uu____8000 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____8001) -> HeadMatch true
        | (uu____8003,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____8007 = FStar_Const.eq_const c d  in
            if uu____8007
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____8017),FStar_Syntax_Syntax.Tm_uvar (uv',uu____8019)) ->
            let uu____8052 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____8052
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____8062),FStar_Syntax_Syntax.Tm_refine (y,uu____8064)) ->
            let uu____8073 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8073 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____8075),uu____8076) ->
            let uu____8081 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____8081 head_match
        | (uu____8082,FStar_Syntax_Syntax.Tm_refine (x,uu____8084)) ->
            let uu____8089 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8089 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8090,FStar_Syntax_Syntax.Tm_type
           uu____8091) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____8093,FStar_Syntax_Syntax.Tm_arrow uu____8094) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____8125),FStar_Syntax_Syntax.Tm_app (head',uu____8127))
            ->
            let uu____8176 = head_matches env head head'  in
            FStar_All.pipe_right uu____8176 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____8178),uu____8179) ->
            let uu____8204 = head_matches env head t21  in
            FStar_All.pipe_right uu____8204 head_match
        | (uu____8205,FStar_Syntax_Syntax.Tm_app (head,uu____8207)) ->
            let uu____8232 = head_matches env t11 head  in
            FStar_All.pipe_right uu____8232 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8233,FStar_Syntax_Syntax.Tm_let
           uu____8234) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____8262,FStar_Syntax_Syntax.Tm_match uu____8263) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8309,FStar_Syntax_Syntax.Tm_abs
           uu____8310) -> HeadMatch true
        | uu____8348 ->
            let uu____8353 =
              let uu____8362 = delta_depth_of_term env t11  in
              let uu____8365 = delta_depth_of_term env t21  in
              (uu____8362, uu____8365)  in
            MisMatch uu____8353
  
let (head_matches_delta :
  FStar_TypeChecker_Env.env ->
    worklist ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
          (match_result * (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ)
            FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun wl  ->
      fun t1  ->
        fun t2  ->
          let maybe_inline t =
            let head =
              let uu____8434 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8434  in
            (let uu____8436 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8436
             then
               let uu____8441 = FStar_Syntax_Print.term_to_string t  in
               let uu____8443 = FStar_Syntax_Print.term_to_string head  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8441 uu____8443
             else ());
            (let uu____8448 =
               let uu____8449 = FStar_Syntax_Util.un_uinst head  in
               uu____8449.FStar_Syntax_Syntax.n  in
             match uu____8448 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8455 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8455 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8469 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8469
                        then
                          let uu____8474 =
                            FStar_Syntax_Print.term_to_string head  in
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
                        FStar_TypeChecker_Env.Iota]  in
                      let steps =
                        if wl.smt_ok
                        then basic_steps
                        else
                          (FStar_TypeChecker_Env.Exclude
                             FStar_TypeChecker_Env.Zeta)
                          :: basic_steps
                         in
                      let t' =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.1" steps env
                          t
                         in
                      let uu____8497 =
                        let uu____8499 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8499 = FStar_Syntax_Util.Equal  in
                      if uu____8497
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8506 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8506
                          then
                            let uu____8511 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8513 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8511
                              uu____8513
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8518 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____8670 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8670
             then
               let uu____8675 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8677 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8679 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8675
                 uu____8677 uu____8679
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8707 =
                 if d1_greater_than_d2
                 then
                   let t1' =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d2;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   (t1', t21)
                 else
                   (let t2' =
                      normalize_refinement
                        [FStar_TypeChecker_Env.UnfoldUntil d1;
                        FStar_TypeChecker_Env.Weak;
                        FStar_TypeChecker_Env.HNF] env t21
                       in
                    (t11, t2'))
                  in
               match uu____8707 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8755 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8755 with
               | FStar_Pervasives_Native.None  -> fail n_delta r1 t11 t21
               | FStar_Pervasives_Native.Some d1 ->
                   let t12 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t11
                      in
                   let t22 =
                     normalize_refinement
                       [FStar_TypeChecker_Env.UnfoldUntil d1;
                       FStar_TypeChecker_Env.Weak;
                       FStar_TypeChecker_Env.HNF] env t21
                      in
                   aux retry (n_delta + Prims.int_one) t12 t22
                in
             match r with
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  i),FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level j))
                 when
                 ((i > Prims.int_zero) || (j > Prims.int_zero)) && (i <> j)
                 ->
                 reduce_one_and_try_again
                   (FStar_Syntax_Syntax.Delta_equational_at_level i)
                   (FStar_Syntax_Syntax.Delta_equational_at_level j)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                  uu____8793),uu____8794)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8815 =
                      let uu____8824 = maybe_inline t11  in
                      let uu____8827 = maybe_inline t21  in
                      (uu____8824, uu____8827)  in
                    match uu____8815 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (uu____8870,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8871))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8892 =
                      let uu____8901 = maybe_inline t11  in
                      let uu____8904 = maybe_inline t21  in
                      (uu____8901, uu____8904)  in
                    match uu____8892 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail n_delta r t11 t21
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.None ) ->
                        aux false (n_delta + Prims.int_one) t12 t21
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t11 t22
                    | (FStar_Pervasives_Native.Some
                       t12,FStar_Pervasives_Native.Some t22) ->
                        aux false (n_delta + Prims.int_one) t12 t22)
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 when d1 = d2 -> reduce_both_and_try_again d1 r
             | MisMatch
                 (FStar_Pervasives_Native.Some
                  d1,FStar_Pervasives_Native.Some d2)
                 -> reduce_one_and_try_again d1 d2
             | MisMatch uu____8959 -> fail n_delta r t11 t21
             | uu____8968 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8983 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8983
           then
             let uu____8988 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8990 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8992 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____9000 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____9017 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____9017
                    (fun uu____9052  ->
                       match uu____9052 with
                       | (t11,t21) ->
                           let uu____9060 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____9062 =
                             let uu____9064 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____9064  in
                           Prims.op_Hat uu____9060 uu____9062))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8988 uu____8990 uu____8992 uu____9000
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____9081 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____9081 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_9096  ->
    match uu___21_9096 with
    | FStar_TypeChecker_Common.Rigid_rigid  -> Prims.int_zero
    | FStar_TypeChecker_Common.Flex_rigid_eq  -> Prims.int_one
    | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> (Prims.of_int (2))
    | FStar_TypeChecker_Common.Flex_rigid  -> (Prims.of_int (3))
    | FStar_TypeChecker_Common.Rigid_flex  -> (Prims.of_int (4))
    | FStar_TypeChecker_Common.Flex_flex  -> (Prims.of_int (5))
  
let (rank_leq :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (rank_t_num r1) <= (rank_t_num r2) 
let (rank_less_than :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Common.rank_t -> Prims.bool)
  = fun r1  -> fun r2  -> (r1 <> r2) && ((rank_t_num r1) <= (rank_t_num r2)) 
let (compress_tprob :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem ->
      FStar_Syntax_Syntax.term FStar_TypeChecker_Common.problem)
  =
  fun tcenv  ->
    fun p  ->
      let uu___1259_9145 = p  in
      let uu____9148 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____9149 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
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
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9164 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____9164
            (fun uu____9169  -> FStar_TypeChecker_Common.TProb uu____9169)
      | FStar_TypeChecker_Common.CProb uu____9170 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____9193 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____9193 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9201 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9201 with
           | (lh,lhs_args) ->
               let uu____9248 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9248 with
                | (rh,rhs_args) ->
                    let uu____9295 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9308,FStar_Syntax_Syntax.Tm_uvar uu____9309)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9398 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9425,uu____9426)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9441,FStar_Syntax_Syntax.Tm_uvar uu____9442)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9457,FStar_Syntax_Syntax.Tm_arrow uu____9458)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9488 = tp  in
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
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9491,FStar_Syntax_Syntax.Tm_type uu____9492)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9508 = tp  in
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
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9511,FStar_Syntax_Syntax.Tm_uvar uu____9512)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9528 = tp  in
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
                      | (uu____9531,FStar_Syntax_Syntax.Tm_uvar uu____9532)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9547,uu____9548)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9563,FStar_Syntax_Syntax.Tm_uvar uu____9564)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9579,uu____9580) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9295 with
                     | (rank,tp1) ->
                         let uu____9593 =
                           FStar_All.pipe_right
                             (let uu___1330_9597 = tp1  in
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
                             (fun uu____9600  ->
                                FStar_TypeChecker_Common.TProb uu____9600)
                            in
                         (rank, uu____9593))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9604 =
            FStar_All.pipe_right
              (let uu___1334_9608 = cp  in
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
              (fun uu____9611  -> FStar_TypeChecker_Common.CProb uu____9611)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9604)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9671 probs =
      match uu____9671 with
      | (min_rank,min,out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9752 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9773 = rank wl.tcenv hd  in
               (match uu____9773 with
                | (rank1,hd1) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStar_List.append out tl), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd1, (FStar_List.append out (m :: tl)), rank1))
                    else
                      (let uu____9834 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9839 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9839)
                          in
                       if uu____9834
                       then
                         match min with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd1), out) tl
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd1), (m ::
                                 out)) tl
                       else aux (min_rank, min, (hd1 :: out)) tl)))
       in
    aux (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None, [])
      wl.attempting
  
let (flex_prob_closing :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_TypeChecker_Common.prob -> Prims.bool)
  =
  fun tcenv  ->
    fun bs  ->
      fun p  ->
        let flex_will_be_closed t =
          let uu____9912 = FStar_Syntax_Util.head_and_args t  in
          match uu____9912 with
          | (hd,uu____9931) ->
              let uu____9956 =
                let uu____9957 = FStar_Syntax_Subst.compress hd  in
                uu____9957.FStar_Syntax_Syntax.n  in
              (match uu____9956 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9962) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9997  ->
                           match uu____9997 with
                           | (y,uu____10006) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____10029  ->
                                       match uu____10029 with
                                       | (x,uu____10038) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____10043 -> false)
           in
        let uu____10045 = rank tcenv p  in
        match uu____10045 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____10054 -> true
             | FStar_TypeChecker_Common.TProb p2 ->
                 (match r with
                  | FStar_TypeChecker_Common.Rigid_rigid  -> true
                  | FStar_TypeChecker_Common.Flex_rigid_eq  -> true
                  | FStar_TypeChecker_Common.Flex_flex_pattern_eq  -> true
                  | FStar_TypeChecker_Common.Flex_rigid  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.lhs
                  | FStar_TypeChecker_Common.Rigid_flex  ->
                      flex_will_be_closed p2.FStar_TypeChecker_Common.rhs
                  | FStar_TypeChecker_Common.Flex_flex  ->
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
  fun projectee  ->
    match projectee with | UDeferred _0 -> true | uu____10135 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____10154 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____10173 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____10190 = FStar_Thunk.mkv s  in UFailed uu____10190 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____10205 = mklstr s  in UFailed uu____10205 
let rec (really_solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun pid_orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          let u11 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1  in
          let u21 =
            FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2  in
          let rec occurs_univ v1 u =
            match u with
            | FStar_Syntax_Syntax.U_max us ->
                FStar_All.pipe_right us
                  (FStar_Util.for_some
                     (fun u3  ->
                        let uu____10256 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____10256 with
                        | (k,uu____10264) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10279 -> false)))
            | uu____10281 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10333 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  FStar_Syntax_Util.eq_univs uv1 uv2))
                           in
                        if uu____10333 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____10357 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  -> FStar_Syntax_Util.eq_univs u u'))
                      in
                   Prims.op_Negation uu____10357)
               in
            let uu____10364 = filter u12  in
            let uu____10367 = filter u22  in (uu____10364, uu____10367)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10402 = filter_out_common_univs us1 us2  in
                   (match uu____10402 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10462 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10462 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10465 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10482  ->
                               let uu____10483 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10485 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10483 uu____10485))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10511 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10511 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10537 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10537 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10540 ->
                   ufailed_thunk
                     (fun uu____10551  ->
                        let uu____10552 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10554 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10552 uu____10554 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10557,uu____10558) ->
              let uu____10560 =
                let uu____10562 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10564 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10562 uu____10564
                 in
              failwith uu____10560
          | (FStar_Syntax_Syntax.U_unknown ,uu____10567) ->
              let uu____10568 =
                let uu____10570 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10572 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10570 uu____10572
                 in
              failwith uu____10568
          | (uu____10575,FStar_Syntax_Syntax.U_bvar uu____10576) ->
              let uu____10578 =
                let uu____10580 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10582 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10580 uu____10582
                 in
              failwith uu____10578
          | (uu____10585,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10586 =
                let uu____10588 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10590 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10588 uu____10590
                 in
              failwith uu____10586
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              let uu____10595 =
                let uu____10597 = FStar_Ident.string_of_id x  in
                let uu____10599 = FStar_Ident.string_of_id y  in
                uu____10597 = uu____10599  in
              if uu____10595
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10630 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10630
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10649 = occurs_univ v1 u3  in
              if uu____10649
              then
                let uu____10652 =
                  let uu____10654 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10656 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10654 uu____10656
                   in
                try_umax_components u11 u21 uu____10652
              else
                (let uu____10661 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10661)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10675 = occurs_univ v1 u3  in
              if uu____10675
              then
                let uu____10678 =
                  let uu____10680 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10682 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10680 uu____10682
                   in
                try_umax_components u11 u21 uu____10678
              else
                (let uu____10687 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10687)
          | (FStar_Syntax_Syntax.U_max uu____10688,uu____10689) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10697 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10697
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10703,FStar_Syntax_Syntax.U_max uu____10704) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10712 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10712
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10718,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10720,FStar_Syntax_Syntax.U_name uu____10721) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10723) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10725) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10727,FStar_Syntax_Syntax.U_succ uu____10728) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10730,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
  
let (solve_universe_eq :
  Prims.int ->
    worklist ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> univ_eq_sol)
  =
  fun orig  ->
    fun wl  ->
      fun u1  ->
        fun u2  ->
          if (wl.tcenv).FStar_TypeChecker_Env.lax_universes
          then USolved wl
          else really_solve_universe_eq orig wl u1 u2
  
let match_num_binders :
  'a 'b .
    ('a Prims.list * ('a Prims.list -> 'b)) ->
      ('a Prims.list * ('a Prims.list -> 'b)) ->
        (('a Prims.list * 'b) * ('a Prims.list * 'b))
  =
  fun bc1  ->
    fun bc2  ->
      let uu____10837 = bc1  in
      match uu____10837 with
      | (bs1,mk_cod1) ->
          let uu____10881 = bc2  in
          (match uu____10881 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10992 = aux xs ys  in
                     (match uu____10992 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____11075 =
                       let uu____11082 = mk_cod1 xs  in ([], uu____11082)  in
                     let uu____11085 =
                       let uu____11092 = mk_cod2 ys  in ([], uu____11092)  in
                     (uu____11075, uu____11085)
                  in
               aux bs1 bs2)
  
let (guard_of_prob :
  FStar_TypeChecker_Env.env ->
    worklist ->
      tprob ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun env  ->
    fun wl  ->
      fun problem  ->
        fun t1  ->
          fun t2  ->
            let has_type_guard t11 t21 =
              match problem.FStar_TypeChecker_Common.element with
              | FStar_Pervasives_Native.Some t ->
                  let uu____11161 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____11161 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____11164 =
                    let uu____11165 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____11165 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____11164
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____11170 = has_type_guard t1 t2  in (uu____11170, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____11171 = has_type_guard t2 t1  in (uu____11171, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_11178  ->
    match uu___22_11178 with
    | Flex (uu____11180,uu____11181,[]) -> true
    | uu____11191 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____11205 = f  in
      match uu____11205 with
      | Flex (uu____11207,u,uu____11209) ->
          FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
            wl.tcenv u
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____11233 = f  in
      match uu____11233 with
      | Flex
          (uu____11240,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____11241;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11242;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____11245;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____11246;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____11247;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____11248;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11314  ->
                 match uu____11314 with
                 | (y,uu____11323) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11477 =
                  let uu____11492 =
                    let uu____11495 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11495  in
                  ((FStar_List.rev pat_binders), uu____11492)  in
                FStar_Pervasives_Native.Some uu____11477
            | (uu____11528,[]) ->
                let uu____11559 =
                  let uu____11574 =
                    let uu____11577 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11577  in
                  ((FStar_List.rev pat_binders), uu____11574)  in
                FStar_Pervasives_Native.Some uu____11559
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11668 =
                  let uu____11669 = FStar_Syntax_Subst.compress a  in
                  uu____11669.FStar_Syntax_Syntax.n  in
                (match uu____11668 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11689 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11689
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1671_11719 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1671_11719.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1671_11719.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11723 =
                            let uu____11724 =
                              let uu____11731 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11731)  in
                            FStar_Syntax_Syntax.NT uu____11724  in
                          [uu____11723]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1677_11747 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1677_11747.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1677_11747.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11748 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11788 =
                  let uu____11795 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11795  in
                (match uu____11788 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11854 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11879 ->
               let uu____11880 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11880 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____12212 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____12212
       then
         let uu____12217 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12217
       else ());
      (let uu____12223 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____12223
       then
         let uu____12228 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12228
       else ());
      (let uu____12233 = next_prob probs  in
       match uu____12233 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1704_12260 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1704_12260.wl_deferred);
               wl_deferred_to_tac = (uu___1704_12260.wl_deferred_to_tac);
               ctr = (uu___1704_12260.ctr);
               defer_ok = (uu___1704_12260.defer_ok);
               smt_ok = (uu___1704_12260.smt_ok);
               umax_heuristic_ok = (uu___1704_12260.umax_heuristic_ok);
               tcenv = (uu___1704_12260.tcenv);
               wl_implicits = (uu___1704_12260.wl_implicits);
               repr_subcomp_allowed = (uu___1704_12260.repr_subcomp_allowed)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12269 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____12269
                 then
                   let uu____12272 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____12272
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
                           (let uu___1716_12284 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1716_12284.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1716_12284.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1716_12284.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1716_12284.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1716_12284.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1716_12284.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1716_12284.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1716_12284.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1716_12284.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12304 =
                  let uu____12311 = as_deferred probs.wl_deferred_to_tac  in
                  ([], uu____12311, (probs.wl_implicits))  in
                Success uu____12304
            | uu____12317 ->
                let uu____12327 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12392  ->
                          match uu____12392 with
                          | (c,uu____12402,uu____12403) -> c < probs.ctr))
                   in
                (match uu____12327 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12451 =
                            let uu____12458 = as_deferred probs.wl_deferred
                               in
                            let uu____12459 =
                              as_deferred probs.wl_deferred_to_tac  in
                            (uu____12458, uu____12459, (probs.wl_implicits))
                             in
                          Success uu____12451
                      | uu____12460 ->
                          let uu____12470 =
                            let uu___1730_12471 = probs  in
                            let uu____12472 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12493  ->
                                      match uu____12493 with
                                      | (uu____12501,uu____12502,y) -> y))
                               in
                            {
                              attempting = uu____12472;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1730_12471.wl_deferred_to_tac);
                              ctr = (uu___1730_12471.ctr);
                              defer_ok = (uu___1730_12471.defer_ok);
                              smt_ok = (uu___1730_12471.smt_ok);
                              umax_heuristic_ok =
                                (uu___1730_12471.umax_heuristic_ok);
                              tcenv = (uu___1730_12471.tcenv);
                              wl_implicits = (uu___1730_12471.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1730_12471.repr_subcomp_allowed)
                            }  in
                          solve env uu____12470))))

and (solve_one_universe_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.universe ->
        FStar_Syntax_Syntax.universe -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun u1  ->
        fun u2  ->
          fun wl  ->
            let uu____12511 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12511 with
            | USolved wl1 ->
                let uu____12513 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12513
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12516 = defer_lit "" orig wl1  in
                solve env uu____12516

and (solve_maybe_uinsts :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> worklist -> univ_eq_sol)
  =
  fun env  ->
    fun orig  ->
      fun t1  ->
        fun t2  ->
          fun wl  ->
            let rec aux wl1 us1 us2 =
              match (us1, us2) with
              | ([],[]) -> USolved wl1
              | (u1::us11,u2::us21) ->
                  let uu____12567 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12567 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12570 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12583;
                  FStar_Syntax_Syntax.vars = uu____12584;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12587;
                  FStar_Syntax_Syntax.vars = uu____12588;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12601,uu____12602) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12610,FStar_Syntax_Syntax.Tm_uinst uu____12611) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12619 -> USolved wl

and (giveup_or_defer :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> lstring -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun msg  ->
          if wl.defer_ok
          then
            ((let uu____12630 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12630
              then
                let uu____12635 = prob_to_string env orig  in
                let uu____12637 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12635 uu____12637
              else ());
             solve env (defer msg orig wl))
          else giveup env msg orig

and (defer_to_user_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> Prims.string -> worklist -> solution)
  =
  fun env  ->
    fun orig  ->
      fun reason  ->
        fun wl  ->
          let wl1 = solve_prob orig FStar_Pervasives_Native.None [] wl  in
          let wl2 =
            let uu___1812_12652 = wl1  in
            let uu____12653 =
              let uu____12663 =
                let uu____12671 = FStar_Thunk.mkv reason  in
                ((wl1.ctr), uu____12671, orig)  in
              uu____12663 :: (wl1.wl_deferred_to_tac)  in
            {
              attempting = (uu___1812_12652.attempting);
              wl_deferred = (uu___1812_12652.wl_deferred);
              wl_deferred_to_tac = uu____12653;
              ctr = (uu___1812_12652.ctr);
              defer_ok = (uu___1812_12652.defer_ok);
              smt_ok = (uu___1812_12652.smt_ok);
              umax_heuristic_ok = (uu___1812_12652.umax_heuristic_ok);
              tcenv = (uu___1812_12652.tcenv);
              wl_implicits = (uu___1812_12652.wl_implicits);
              repr_subcomp_allowed = (uu___1812_12652.repr_subcomp_allowed)
            }  in
          solve env wl2

and (maybe_defer_to_user_tac :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem ->
      Prims.string -> worklist -> solution)
  =
  fun env  ->
    fun prob  ->
      fun reason  ->
        fun wl  ->
          match prob.FStar_TypeChecker_Common.relation with
          | FStar_TypeChecker_Common.EQ  ->
              let should_defer_tac t =
                let uu____12700 = FStar_Syntax_Util.head_and_args t  in
                match uu____12700 with
                | (head,uu____12724) ->
                    let uu____12749 =
                      let uu____12750 = FStar_Syntax_Subst.compress head  in
                      uu____12750.FStar_Syntax_Syntax.n  in
                    (match uu____12749 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12760) ->
                         let uu____12777 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv
                            in
                         (uu____12777,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12781 -> (false, ""))
                 in
              let uu____12786 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs  in
              (match uu____12786 with
               | (l1,r1) ->
                   let uu____12799 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs  in
                   (match uu____12799 with
                    | (l2,r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12816 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl
                              in
                           solve env uu____12816)))
          | uu____12817 ->
              let uu____12818 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl  in
              solve env uu____12818

and (solve_rigid_flex_or_flex_rigid_subtyping :
  FStar_TypeChecker_Common.rank_t ->
    FStar_TypeChecker_Env.env -> tprob -> worklist -> solution)
  =
  fun rank1  ->
    fun env  ->
      fun tp  ->
        fun wl  ->
          def_check_prob "solve_rigid_flex_or_flex_rigid_subtyping"
            (FStar_TypeChecker_Common.TProb tp);
          (let flip = rank1 = FStar_TypeChecker_Common.Flex_rigid  in
           let meet_or_join op ts env1 wl1 =
             let eq_prob t1 t2 wl2 =
               let uu____12904 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12904 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12959 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12959
                then
                  let uu____12964 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12966 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12964 uu____12966
                else ());
               (let uu____12971 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12971 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____13017 = eq_prob t1 t2 wl2  in
                         (match uu____13017 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____13038 ->
                         let uu____13047 = eq_prob t1 t2 wl2  in
                         (match uu____13047 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13097 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13112 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13113 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13112, uu____13113)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13118 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13119 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13118, uu____13119)
                            in
                         (match uu____13097 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13150 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13150 with
                                | (t1_hd,t1_args) ->
                                    let uu____13195 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13195 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13261 =
                                              let uu____13268 =
                                                let uu____13279 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____13279 :: t1_args  in
                                              let uu____13296 =
                                                let uu____13305 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____13305 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____13354  ->
                                                   fun uu____13355  ->
                                                     fun uu____13356  ->
                                                       match (uu____13354,
                                                               uu____13355,
                                                               uu____13356)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____13406),
                                                          (a2,uu____13408))
                                                           ->
                                                           let uu____13445 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13445
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13268
                                                uu____13296
                                               in
                                            match uu____13261 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1915_13471 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1915_13471.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1915_13471.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1915_13471.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1915_13471.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1915_13471.repr_subcomp_allowed)
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13482 =
                                                  solve env1 wl'  in
                                                (match uu____13482 with
                                                 | Success
                                                     (uu____13485,defer_to_tac,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13489 =
                                                         extend_wl wl4
                                                           defer_to_tac imps
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13489))
                                                 | Failed uu____13490 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13522 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13522 with
                                | (t1_base,p1_opt) ->
                                    let uu____13558 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13558 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13657 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13657
                                             then x.FStar_Syntax_Syntax.sort
                                             else
                                               FStar_Syntax_Util.refine x t
                                              in
                                           match (p1_opt1, p2_opt1) with
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi1),FStar_Pervasives_Native.Some
                                              (y,phi2)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi2
                                                  in
                                               let uu____13710 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13710
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi
                                                  in
                                               let uu____13742 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13742
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst phi
                                                  in
                                               let uu____13774 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13774
                                           | uu____13777 -> t_base  in
                                         let uu____13794 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13794 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13808 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13808, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13815 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13815 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13851 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13851 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13887 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13887
                                                         with
                                                         | (p,wl4) ->
                                                             let t =
                                                               combine_refinements
                                                                 t1_base1
                                                                 p1_opt1
                                                                 p2_opt1
                                                                in
                                                             (t, [p], wl4))))))
                                 in
                              let uu____13911 = combine t11 t21 wl2  in
                              (match uu____13911 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13944 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13944
                                     then
                                       let uu____13949 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13949
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13991 ts1 =
               match uu____13991 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____14054 = pairwise out t wl2  in
                        (match uu____14054 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14090 =
               let uu____14101 = FStar_List.hd ts  in (uu____14101, [], wl1)
                in
             let uu____14110 = FStar_List.tl ts  in
             aux uu____14090 uu____14110  in
           let uu____14117 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14117 with
           | (this_flex,this_rigid) ->
               let uu____14143 =
                 let uu____14144 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14144.FStar_Syntax_Syntax.n  in
               (match uu____14143 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14169 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14169
                    then
                      let uu____14172 = destruct_flex_t this_flex wl  in
                      (match uu____14172 with
                       | (flex,wl1) ->
                           let uu____14179 = quasi_pattern env flex  in
                           (match uu____14179 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____14198 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14198
                                  then
                                    let uu____14203 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14203
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14210 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2025_14213 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2025_14213.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2025_14213.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2025_14213.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2025_14213.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2025_14213.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2025_14213.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2025_14213.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2025_14213.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2025_14213.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14210)
                | uu____14214 ->
                    ((let uu____14216 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14216
                      then
                        let uu____14221 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14221
                      else ());
                     (let uu____14226 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14226 with
                      | (u,_args) ->
                          let uu____14269 =
                            let uu____14270 = FStar_Syntax_Subst.compress u
                               in
                            uu____14270.FStar_Syntax_Syntax.n  in
                          (match uu____14269 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____14298 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____14298 with
                                 | (u',uu____14317) ->
                                     let uu____14342 =
                                       let uu____14343 = whnf env u'  in
                                       uu____14343.FStar_Syntax_Syntax.n  in
                                     (match uu____14342 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14365 -> false)
                                  in
                               let uu____14367 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_14390  ->
                                         match uu___23_14390 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1  in
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
                                              | uu____14404 -> false)
                                         | uu____14408 -> false))
                                  in
                               (match uu____14367 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14423 = whnf env this_rigid
                                         in
                                      let uu____14424 =
                                        FStar_List.collect
                                          (fun uu___24_14430  ->
                                             match uu___24_14430 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14436 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14436]
                                             | uu____14440 -> [])
                                          bounds_probs
                                         in
                                      uu____14423 :: uu____14424  in
                                    let uu____14441 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14441 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14474 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14489 =
                                               let uu____14490 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14490.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14489 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14502 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14502)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14513 -> bound  in
                                           let uu____14514 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14514)  in
                                         (match uu____14474 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14549 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14549
                                                then
                                                  let wl'1 =
                                                    let uu___2085_14555 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2085_14555.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2085_14555.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2085_14555.ctr);
                                                      defer_ok =
                                                        (uu___2085_14555.defer_ok);
                                                      smt_ok =
                                                        (uu___2085_14555.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2085_14555.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2085_14555.tcenv);
                                                      wl_implicits =
                                                        (uu___2085_14555.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2085_14555.repr_subcomp_allowed)
                                                    }  in
                                                  let uu____14556 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14556
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14562 =
                                                  solve_t env eq_prob
                                                    (let uu___2090_14564 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2090_14564.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2090_14564.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2090_14564.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2090_14564.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2090_14564.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2090_14564.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2090_14564.repr_subcomp_allowed)
                                                     })
                                                   in
                                                match uu____14562 with
                                                | Success
                                                    (uu____14566,defer_to_tac,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2097_14570 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2097_14570.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2097_14570.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2097_14570.ctr);
                                                        defer_ok =
                                                          (uu___2097_14570.defer_ok);
                                                        smt_ok =
                                                          (uu___2097_14570.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2097_14570.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2097_14570.tcenv);
                                                        wl_implicits =
                                                          (uu___2097_14570.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2097_14570.repr_subcomp_allowed)
                                                      }  in
                                                    let wl3 =
                                                      extend_wl wl2
                                                        defer_to_tac imps
                                                       in
                                                    let g =
                                                      FStar_List.fold_left
                                                        (fun g  ->
                                                           fun p  ->
                                                             FStar_Syntax_Util.mk_conj
                                                               g (p_guard p))
                                                        eq_prob.FStar_TypeChecker_Common.logical_guard
                                                        sub_probs
                                                       in
                                                    let wl4 =
                                                      solve_prob' false
                                                        (FStar_TypeChecker_Common.TProb
                                                           tp)
                                                        (FStar_Pervasives_Native.Some
                                                           g) [] wl3
                                                       in
                                                    let uu____14587 =
                                                      FStar_List.fold_left
                                                        (fun wl5  ->
                                                           fun p  ->
                                                             solve_prob' true
                                                               p
                                                               FStar_Pervasives_Native.None
                                                               [] wl5) wl4
                                                        bounds_probs
                                                       in
                                                    (FStar_Syntax_Unionfind.commit
                                                       tx;
                                                     solve env wl4)
                                                | Failed (p,msg) ->
                                                    ((let uu____14599 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14599
                                                      then
                                                        let uu____14604 =
                                                          let uu____14606 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14606
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14604
                                                      else ());
                                                     (let uu____14619 =
                                                        let uu____14634 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14634)
                                                         in
                                                      match uu____14619 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14656))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14682 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14682
                                                            with
                                                            | (eq_prob1,wl2)
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
                                                                    [] wl2
                                                                     in
                                                                  let uu____14702
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14702))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14727 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14727
                                                            with
                                                            | (eq_prob1,wl2)
                                                                ->
                                                                (def_check_prob
                                                                   "meet_or_join4"
                                                                   (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1);
                                                                 (let phi1 =
                                                                    guard_on_element
                                                                    wl2 tp x
                                                                    phi  in
                                                                  let wl3 =
                                                                    let uu____14747
                                                                    =
                                                                    let uu____14752
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14752
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14747
                                                                    [] wl2
                                                                     in
                                                                  let uu____14758
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14758))))
                                                      | uu____14759 ->
                                                          let uu____14774 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14774 p)))))))
                           | uu____14781 when flip ->
                               let uu____14782 =
                                 let uu____14784 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14786 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14784 uu____14786
                                  in
                               failwith uu____14782
                           | uu____14789 ->
                               let uu____14790 =
                                 let uu____14792 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14794 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14792 uu____14794
                                  in
                               failwith uu____14790)))))

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
  fun orig  ->
    fun env  ->
      fun wl  ->
        fun lhs  ->
          fun bs_lhs  ->
            fun t_res_lhs  ->
              fun rel  ->
                fun arrow  ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____14830  ->
                         match uu____14830 with
                         | (x,i) ->
                             let uu____14849 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14849, i)) bs_lhs
                     in
                  let uu____14852 = lhs  in
                  match uu____14852 with
                  | Flex (uu____14853,u_lhs,uu____14855) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14952 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14962 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14962, univ)
                             in
                          match uu____14952 with
                          | (k,univ) ->
                              let uu____14969 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14969 with
                               | (uu____14986,u,wl3) ->
                                   let uu____14989 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14989, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____15015 =
                              let uu____15028 =
                                let uu____15039 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____15039 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15090  ->
                                   fun uu____15091  ->
                                     match (uu____15090, uu____15091) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15192 =
                                           let uu____15199 =
                                             let uu____15202 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15202
                                              in
                                           copy_uvar u_lhs [] uu____15199 wl2
                                            in
                                         (match uu____15192 with
                                          | (uu____15231,t_a,wl3) ->
                                              let uu____15234 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____15234 with
                                               | (uu____15253,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____15028
                                ([], wl1)
                               in
                            (match uu____15015 with
                             | (out_args,wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_15322  ->
                                        match uu___25_15322 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____15324 -> false
                                        | uu____15328 -> true) flags
                                    in
                                 let ct' =
                                   let uu___2216_15331 = ct  in
                                   let uu____15332 =
                                     let uu____15335 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____15335
                                      in
                                   let uu____15350 = FStar_List.tl out_args
                                      in
                                   let uu____15367 =
                                     nodec ct.FStar_Syntax_Syntax.flags  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2216_15331.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2216_15331.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15332;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15350;
                                     FStar_Syntax_Syntax.flags = uu____15367
                                   }  in
                                 ((let uu___2219_15371 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2219_15371.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2219_15371.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____15374 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____15374 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15412 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____15412 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15423 =
                                          let uu____15428 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15428)  in
                                        TERM uu____15423  in
                                      let uu____15429 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15429 with
                                       | (sub_prob,wl3) ->
                                           let uu____15443 =
                                             let uu____15444 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15444
                                              in
                                           solve env uu____15443))
                             | (x,imp)::formals2 ->
                                 let uu____15466 =
                                   let uu____15473 =
                                     let uu____15476 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15476
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15473 wl1
                                    in
                                 (match uu____15466 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15497 =
                                          let uu____15500 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15500
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15497 u_x
                                         in
                                      let uu____15501 =
                                        let uu____15504 =
                                          let uu____15507 =
                                            let uu____15508 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15508, imp)  in
                                          [uu____15507]  in
                                        FStar_List.append bs_terms
                                          uu____15504
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15501 formals2 wl2)
                              in
                           let uu____15535 = occurs_check u_lhs arrow  in
                           (match uu____15535 with
                            | (uu____15548,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15564 =
                                    mklstr
                                      (fun uu____15569  ->
                                         let uu____15570 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15570)
                                     in
                                  giveup_or_defer env orig wl uu____15564
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
  fun env  ->
    fun bs1  ->
      fun bs2  ->
        fun orig  ->
          fun wl  ->
            fun rhs  ->
              (let uu____15603 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15603
               then
                 let uu____15608 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15611 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15608 (rel_to_string (p_rel orig)) uu____15611
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15742 = rhs wl1 scope env1 subst  in
                     (match uu____15742 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15765 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15765
                            then
                              let uu____15770 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15770
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15848 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15848 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2289_15850 = hd1  in
                       let uu____15851 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2289_15850.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2289_15850.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15851
                       }  in
                     let hd21 =
                       let uu___2292_15855 = hd2  in
                       let uu____15856 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2292_15855.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2292_15855.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15856
                       }  in
                     let uu____15859 =
                       let uu____15864 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15864
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15859 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15887 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15887
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15894 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15894 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15966 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15966
                                  in
                               ((let uu____15984 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15984
                                 then
                                   let uu____15989 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15991 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15989
                                     uu____15991
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____16026 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____16062 = aux wl [] env [] bs1 bs2  in
               match uu____16062 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16121 = attempt sub_probs wl2  in
                   solve env1 uu____16121)

and (try_solve_without_smt_or_else :
  FStar_TypeChecker_Env.env ->
    worklist ->
      (FStar_TypeChecker_Env.env -> worklist -> solution) ->
        (FStar_TypeChecker_Env.env ->
           worklist -> (FStar_TypeChecker_Common.prob * lstring) -> solution)
          -> solution)
  =
  fun env  ->
    fun wl  ->
      fun try_solve  ->
        fun else_solve  ->
          let wl' =
            let uu___2330_16141 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2330_16141.wl_deferred_to_tac);
              ctr = (uu___2330_16141.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2330_16141.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2330_16141.repr_subcomp_allowed)
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16153 = try_solve env wl'  in
          match uu____16153 with
          | Success (uu____16154,defer_to_tac,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps  in solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16167 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16167 wl)

and (solve_t_flex_rigid_eq :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      worklist -> flex_t -> FStar_Syntax_Syntax.term -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            let uu____16173 = should_defer_flex_to_user_tac wl lhs  in
            if uu____16173
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16186 =
                   FStar_List.map FStar_Pervasives_Native.fst bs  in
                 FStar_Util.as_set uu____16186 FStar_Syntax_Syntax.order_bv
                  in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16220 = lhs1  in
                 match uu____16220 with
                 | Flex (uu____16223,ctx_u,uu____16225) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16233 ->
                           let uu____16234 = sn_binders env1 bs  in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16234 rhs1
                        in
                     [TERM (ctx_u, sol)]
                  in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16283 = quasi_pattern env1 lhs1  in
                 match uu____16283 with
                 | FStar_Pervasives_Native.None  ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs,uu____16317) ->
                     let uu____16322 = lhs1  in
                     (match uu____16322 with
                      | Flex (t_lhs,ctx_u,args) ->
                          let uu____16337 = occurs_check ctx_u rhs1  in
                          (match uu____16337 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16388 =
                                   let uu____16396 =
                                     let uu____16398 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16398
                                      in
                                   FStar_Util.Inl uu____16396  in
                                 (uu____16388, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs)
                                     in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1
                                     in
                                  let uu____16426 =
                                    let uu____16428 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs
                                       in
                                    Prims.op_Negation uu____16428  in
                                  if uu____16426
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16455 =
                                       let uu____16463 =
                                         mk_solution env1 lhs1 bs rhs1  in
                                       FStar_Util.Inr uu____16463  in
                                     let uu____16469 =
                                       restrict_all_uvars ctx_u uvars wl1  in
                                     (uu____16455, uu____16469)))))
                  in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16513 = FStar_Syntax_Util.head_and_args rhs1  in
                 match uu____16513 with
                 | (rhs_hd,args) ->
                     let uu____16556 = FStar_Util.prefix args  in
                     (match uu____16556 with
                      | (args_rhs,last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              rhs1.FStar_Syntax_Syntax.pos
                             in
                          let uu____16626 = lhs1  in
                          (match uu____16626 with
                           | Flex (t_lhs,u_lhs,_lhs_args) ->
                               let uu____16630 =
                                 let uu____16641 =
                                   let uu____16648 =
                                     let uu____16651 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16651
                                      in
                                   copy_uvar u_lhs [] uu____16648 wl1  in
                                 match uu____16641 with
                                 | (uu____16678,t_last_arg,wl2) ->
                                     let uu____16681 =
                                       let uu____16688 =
                                         let uu____16689 =
                                           let uu____16698 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg
                                              in
                                           [uu____16698]  in
                                         FStar_List.append bs_lhs uu____16689
                                          in
                                       copy_uvar u_lhs uu____16688 t_res_lhs
                                         wl2
                                        in
                                     (match uu____16681 with
                                      | (uu____16733,lhs',wl3) ->
                                          let uu____16736 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3
                                             in
                                          (match uu____16736 with
                                           | (uu____16753,lhs'_last_arg,wl4)
                                               -> (lhs', lhs'_last_arg, wl4)))
                                  in
                               (match uu____16630 with
                                | (lhs',lhs'_last_arg,wl2) ->
                                    let sol =
                                      let uu____16774 =
                                        let uu____16775 =
                                          let uu____16780 =
                                            let uu____16781 =
                                              let uu____16784 =
                                                let uu____16785 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    lhs'_last_arg
                                                   in
                                                [uu____16785]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                lhs' uu____16784
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16781
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16780)  in
                                        TERM uu____16775  in
                                      [uu____16774]  in
                                    let uu____16810 =
                                      let uu____16817 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs"
                                         in
                                      match uu____16817 with
                                      | (p1,wl3) ->
                                          let uu____16837 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs"
                                             in
                                          (match uu____16837 with
                                           | (p2,wl4) -> ([p1; p2], wl4))
                                       in
                                    (match uu____16810 with
                                     | (sub_probs,wl3) ->
                                         let uu____16869 =
                                           let uu____16870 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16870  in
                                         solve env1 uu____16869))))
                  in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16904 = FStar_Syntax_Util.head_and_args rhs2  in
                   match uu____16904 with
                   | (uu____16922,args) ->
                       (match args with | [] -> false | uu____16958 -> true)
                    in
                 let is_arrow rhs2 =
                   let uu____16977 =
                     let uu____16978 = FStar_Syntax_Subst.compress rhs2  in
                     uu____16978.FStar_Syntax_Syntax.n  in
                   match uu____16977 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____16982 -> true
                   | uu____16998 -> false  in
                 let uu____17000 = quasi_pattern env1 lhs1  in
                 match uu____17000 with
                 | FStar_Pervasives_Native.None  ->
                     let msg =
                       mklstr
                         (fun uu____17019  ->
                            let uu____17020 = prob_to_string env1 orig1  in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____17020)
                        in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                     let uu____17029 = is_app rhs1  in
                     if uu____17029
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____17034 = is_arrow rhs1  in
                        if uu____17034
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu____17047  ->
                                  let uu____17048 = prob_to_string env1 orig1
                                     in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____17048)
                              in
                           giveup_or_defer env1 orig1 wl1 msg))
                  in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB  ->
                   if wl.defer_ok
                   then
                     let uu____17052 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____17052
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV  ->
                   if wl.defer_ok
                   then
                     let uu____17058 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____17058
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ  ->
                   let uu____17063 = lhs  in
                   (match uu____17063 with
                    | Flex (_t1,ctx_uv,args_lhs) ->
                        let uu____17067 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs
                           in
                        (match uu____17067 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs  in
                             let names_to_string1 fvs =
                               let uu____17085 =
                                 let uu____17089 =
                                   FStar_Util.set_elements fvs  in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____17089
                                  in
                               FStar_All.pipe_right uu____17085
                                 (FStar_String.concat ", ")
                                in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders)
                                in
                             let fvs2 = FStar_Syntax_Free.names rhs1  in
                             let uu____17110 = occurs_check ctx_uv rhs1  in
                             (match uu____17110 with
                              | (uvars,occurs_ok,msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17139 =
                                      let uu____17140 =
                                        let uu____17142 =
                                          FStar_Option.get msg  in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17142
                                         in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17140
                                       in
                                    giveup_or_defer env orig wl uu____17139
                                  else
                                    (let uu____17150 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1
                                        in
                                     if uu____17150
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1
                                          in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars wl
                                          in
                                       let uu____17157 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1
                                          in
                                       solve env uu____17157
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            mklstr
                                              (fun uu____17173  ->
                                                 let uu____17174 =
                                                   names_to_string1 fvs2  in
                                                 let uu____17176 =
                                                   names_to_string1 fvs1  in
                                                 let uu____17178 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders)
                                                    in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17174 uu____17176
                                                   uu____17178)
                                             in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17190 ->
                             if wl.defer_ok
                             then
                               let uu____17194 =
                                 FStar_Thunk.mkv "Not a pattern"  in
                               giveup_or_defer env orig wl uu____17194
                             else
                               (let uu____17199 =
                                  try_quasi_pattern orig env wl lhs rhs  in
                                match uu____17199 with
                                | (FStar_Util.Inr sol,wl1) ->
                                    let uu____17225 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17225
                                | (FStar_Util.Inl msg,uu____17227) ->
                                    first_order orig env wl lhs rhs))))

and (solve_t_flex_flex :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> worklist -> flex_t -> flex_t -> solution)
  =
  fun env  ->
    fun orig  ->
      fun wl  ->
        fun lhs  ->
          fun rhs  ->
            match p_rel orig with
            | FStar_TypeChecker_Common.SUB  ->
                if wl.defer_ok
                then
                  let uu____17245 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17245
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____17251 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17251
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17256 =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs)
                   in
                if uu____17256
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
                    (let uu____17263 =
                       FStar_Thunk.mkv "flex-flex non-pattern"  in
                     giveup_or_defer env orig wl uu____17263)
                  else
                    (let uu____17268 =
                       let uu____17285 = quasi_pattern env lhs  in
                       let uu____17292 = quasi_pattern env rhs  in
                       (uu____17285, uu____17292)  in
                     match uu____17268 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                        (binders_rhs,t_res_rhs)) ->
                         let uu____17335 = lhs  in
                         (match uu____17335 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17336;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17338;_},u_lhs,uu____17340)
                              ->
                              let uu____17343 = rhs  in
                              (match uu____17343 with
                               | Flex (uu____17344,u_rhs,uu____17346) ->
                                   let uu____17347 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs)
                                      in
                                   if uu____17347
                                   then
                                     let uu____17354 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl
                                        in
                                     solve env uu____17354
                                   else
                                     (let uu____17357 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      match uu____17357 with
                                      | (ctx_w,(ctx_l,ctx_r)) ->
                                          let gamma_w =
                                            gamma_until
                                              u_lhs.FStar_Syntax_Syntax.ctx_uvar_gamma
                                              ctx_w
                                             in
                                          let zs =
                                            intersect_binders gamma_w
                                              (FStar_List.append ctx_l
                                                 binders_lhs)
                                              (FStar_List.append ctx_r
                                                 binders_rhs)
                                             in
                                          let uu____17389 =
                                            let uu____17396 =
                                              let uu____17399 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs
                                                 in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17399
                                               in
                                            new_uvar
                                              (Prims.op_Hat
                                                 "flex-flex quasi:"
                                                 (Prims.op_Hat "\tlhs="
                                                    (Prims.op_Hat
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_reason
                                                       (Prims.op_Hat "\trhs="
                                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_reason))))
                                              wl range gamma_w ctx_w
                                              uu____17396
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None
                                             in
                                          (match uu____17389 with
                                           | (uu____17405,w,wl1) ->
                                               let w_app =
                                                 let uu____17409 =
                                                   FStar_List.map
                                                     (fun uu____17420  ->
                                                        match uu____17420
                                                        with
                                                        | (z,uu____17428) ->
                                                            let uu____17433 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____17433) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____17409
                                                   w.FStar_Syntax_Syntax.pos
                                                  in
                                               ((let uu____17435 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17435
                                                 then
                                                   let uu____17440 =
                                                     let uu____17444 =
                                                       flex_t_to_string lhs
                                                        in
                                                     let uu____17446 =
                                                       let uu____17450 =
                                                         flex_t_to_string rhs
                                                          in
                                                       let uu____17452 =
                                                         let uu____17456 =
                                                           term_to_string w
                                                            in
                                                         let uu____17458 =
                                                           let uu____17462 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs)
                                                              in
                                                           let uu____17471 =
                                                             let uu____17475
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                in
                                                             let uu____17484
                                                               =
                                                               let uu____17488
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs
                                                                  in
                                                               [uu____17488]
                                                                in
                                                             uu____17475 ::
                                                               uu____17484
                                                              in
                                                           uu____17462 ::
                                                             uu____17471
                                                            in
                                                         uu____17456 ::
                                                           uu____17458
                                                          in
                                                       uu____17450 ::
                                                         uu____17452
                                                        in
                                                     uu____17444 ::
                                                       uu____17446
                                                      in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17440
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17505 =
                                                       let uu____17510 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs))
                                                          in
                                                       (u_lhs, uu____17510)
                                                        in
                                                     TERM uu____17505  in
                                                   let uu____17511 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                      in
                                                   if uu____17511
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17519 =
                                                          let uu____17524 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_rhs,
                                                            uu____17524)
                                                           in
                                                        TERM uu____17519  in
                                                      [s1; s2])
                                                    in
                                                 let uu____17525 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1
                                                    in
                                                 solve env uu____17525))))))
                     | uu____17526 ->
                         let uu____17543 =
                           FStar_Thunk.mkv "flex-flex: non-patterns"  in
                         giveup_or_defer env orig wl uu____17543)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17597 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17597
            then
              let uu____17602 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17604 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17606 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17608 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17602 uu____17604 uu____17606 uu____17608
            else ());
           (let uu____17619 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17619 with
            | (head1,args1) ->
                let uu____17662 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17662 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17732 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17732 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17737 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17737)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17758 =
                         mklstr
                           (fun uu____17769  ->
                              let uu____17770 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17772 = args_to_string args1  in
                              let uu____17776 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17778 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17770 uu____17772 uu____17776
                                uu____17778)
                          in
                       giveup env1 uu____17758 orig
                     else
                       (let uu____17785 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17790 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17790 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17785
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2602_17794 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2602_17794.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2602_17794.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2602_17794.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2602_17794.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2602_17794.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2602_17794.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2602_17794.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2602_17794.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17804 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17804
                                    else solve env1 wl2))
                        else
                          (let uu____17809 = base_and_refinement env1 t1  in
                           match uu____17809 with
                           | (base1,refinement1) ->
                               let uu____17834 = base_and_refinement env1 t2
                                  in
                               (match uu____17834 with
                                | (base2,refinement2) ->
                                    (match (refinement1, refinement2) with
                                     | (FStar_Pervasives_Native.None
                                        ,FStar_Pervasives_Native.None ) ->
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
                                             else FStar_List.zip args1 args2
                                              in
                                           let uu____17999 =
                                             FStar_List.fold_right
                                               (fun uu____18039  ->
                                                  fun uu____18040  ->
                                                    match (uu____18039,
                                                            uu____18040)
                                                    with
                                                    | (((a1,uu____18092),
                                                        (a2,uu____18094)),
                                                       (probs,wl3)) ->
                                                        let uu____18143 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18143
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17999 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18186 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18186
                                                 then
                                                   let uu____18191 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18191
                                                 else ());
                                                (let uu____18197 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18197
                                                 then
                                                   FStar_List.iter
                                                     (def_check_prob
                                                        "solve_t' subprobs")
                                                     subprobs
                                                 else ());
                                                (subprobs, wl3))
                                            in
                                         let solve_sub_probs env2 wl2 =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  if Prims.op_Negation ok
                                                  then solve env2 wl3
                                                  else
                                                    (let uu____18224 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18224 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18240 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18240
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18248 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18248))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18273 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18273 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18289 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18289
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18297 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18297)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18325 =
                                           match uu____18325 with
                                           | (prob,reason) ->
                                               ((let uu____18342 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18342
                                                 then
                                                   let uu____18347 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18349 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____18347 uu____18349
                                                 else ());
                                                (let uu____18355 =
                                                   let uu____18364 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18367 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18364, uu____18367)
                                                    in
                                                 match uu____18355 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18380 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18380 with
                                                      | (head1',uu____18398)
                                                          ->
                                                          let uu____18423 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18423
                                                           with
                                                           | (head2',uu____18441)
                                                               ->
                                                               let uu____18466
                                                                 =
                                                                 let uu____18471
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18472
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18471,
                                                                   uu____18472)
                                                                  in
                                                               (match uu____18466
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18474
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18474
                                                                    then
                                                                    let uu____18479
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18481
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18483
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18485
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18479
                                                                    uu____18481
                                                                    uu____18483
                                                                    uu____18485
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18490
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2690_18498
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2690_18498.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2690_18498.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2690_18498.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2690_18498.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2690_18498.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2690_18498.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2690_18498.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2690_18498.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18500
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18500
                                                                    then
                                                                    let uu____18505
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18505
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18510 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18522 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18522 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18530 =
                                             let uu____18531 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18531.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18530 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18536 -> false  in
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
                                          | uu____18539 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18542 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2710_18578 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2710_18578.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2710_18578.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2710_18578.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2710_18578.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2710_18578.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2710_18578.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2710_18578.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2710_18578.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18654 = destruct_flex_t scrutinee wl1  in
             match uu____18654 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____18665 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18665 with
                  | (xs,pat_term,uu____18681,uu____18682) ->
                      let uu____18687 =
                        FStar_List.fold_left
                          (fun uu____18710  ->
                             fun x  ->
                               match uu____18710 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18731 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18731 with
                                    | (uu____18750,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18687 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18771 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18771 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2751_18788 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2751_18788.wl_deferred_to_tac);
                                    ctr = (uu___2751_18788.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2751_18788.umax_heuristic_ok);
                                    tcenv = (uu___2751_18788.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2751_18788.repr_subcomp_allowed)
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18799 = solve env1 wl'  in
                                (match uu____18799 with
                                 | Success (uu____18802,defer_to_tac,imps) ->
                                     let wl'1 =
                                       let uu___2760_18806 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2760_18806.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2760_18806.wl_deferred_to_tac);
                                         ctr = (uu___2760_18806.ctr);
                                         defer_ok =
                                           (uu___2760_18806.defer_ok);
                                         smt_ok = (uu___2760_18806.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2760_18806.umax_heuristic_ok);
                                         tcenv = (uu___2760_18806.tcenv);
                                         wl_implicits =
                                           (uu___2760_18806.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2760_18806.repr_subcomp_allowed)
                                       }  in
                                     let uu____18807 = solve env1 wl'1  in
                                     (match uu____18807 with
                                      | Success
                                          (uu____18810,defer_to_tac',imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18814 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps')
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____18814))
                                      | Failed uu____18820 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18826 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18849 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18849
                 then
                   let uu____18854 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18856 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18854 uu____18856
                 else ());
                (let uu____18861 =
                   let uu____18882 =
                     let uu____18891 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18891)  in
                   let uu____18898 =
                     let uu____18907 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18907)  in
                   (uu____18882, uu____18898)  in
                 match uu____18861 with
                 | ((uu____18937,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18940;
                                   FStar_Syntax_Syntax.vars = uu____18941;_}),
                    (s,t)) ->
                     let uu____19012 =
                       let uu____19014 = is_flex scrutinee  in
                       Prims.op_Negation uu____19014  in
                     if uu____19012
                     then
                       ((let uu____19025 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19025
                         then
                           let uu____19030 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19030
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19049 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19049
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19064 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19064
                           then
                             let uu____19069 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19071 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19069 uu____19071
                           else ());
                          (let pat_discriminates uu___26_19096 =
                             match uu___26_19096 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19112;
                                  FStar_Syntax_Syntax.p = uu____19113;_},FStar_Pervasives_Native.None
                                ,uu____19114) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19128;
                                  FStar_Syntax_Syntax.p = uu____19129;_},FStar_Pervasives_Native.None
                                ,uu____19130) -> true
                             | uu____19157 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19260 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19260 with
                                       | (uu____19262,uu____19263,t') ->
                                           let uu____19281 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19281 with
                                            | (FullMatch ,uu____19293) ->
                                                true
                                            | (HeadMatch
                                               uu____19307,uu____19308) ->
                                                true
                                            | uu____19323 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19360 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19360
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19371 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19371 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19459,uu____19460) ->
                                       branches1
                                   | uu____19605 -> branches  in
                                 let uu____19660 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19669 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19669 with
                                        | (p,uu____19673,uu____19674) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19703  ->
                                      FStar_Util.Inr uu____19703) uu____19660))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19733 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19733 with
                                | (p,uu____19742,e) ->
                                    ((let uu____19761 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19761
                                      then
                                        let uu____19766 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19768 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19766 uu____19768
                                      else ());
                                     (let uu____19773 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19788  ->
                                           FStar_Util.Inr uu____19788)
                                        uu____19773)))))
                 | ((s,t),(uu____19791,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19794;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19795;_}))
                     ->
                     let uu____19864 =
                       let uu____19866 = is_flex scrutinee  in
                       Prims.op_Negation uu____19866  in
                     if uu____19864
                     then
                       ((let uu____19877 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19877
                         then
                           let uu____19882 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19882
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19901 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19901
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19916 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19916
                           then
                             let uu____19921 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19923 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19921 uu____19923
                           else ());
                          (let pat_discriminates uu___26_19948 =
                             match uu___26_19948 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19964;
                                  FStar_Syntax_Syntax.p = uu____19965;_},FStar_Pervasives_Native.None
                                ,uu____19966) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19980;
                                  FStar_Syntax_Syntax.p = uu____19981;_},FStar_Pervasives_Native.None
                                ,uu____19982) -> true
                             | uu____20009 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20112 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20112 with
                                       | (uu____20114,uu____20115,t') ->
                                           let uu____20133 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20133 with
                                            | (FullMatch ,uu____20145) ->
                                                true
                                            | (HeadMatch
                                               uu____20159,uu____20160) ->
                                                true
                                            | uu____20175 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20212 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20212
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20223 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20223 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20311,uu____20312) ->
                                       branches1
                                   | uu____20457 -> branches  in
                                 let uu____20512 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20521 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20521 with
                                        | (p,uu____20525,uu____20526) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____20555  ->
                                      FStar_Util.Inr uu____20555) uu____20512))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20585 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20585 with
                                | (p,uu____20594,e) ->
                                    ((let uu____20613 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20613
                                      then
                                        let uu____20618 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20620 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20618 uu____20620
                                      else ());
                                     (let uu____20625 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____20640  ->
                                           FStar_Util.Inr uu____20640)
                                        uu____20625)))))
                 | uu____20641 ->
                     ((let uu____20663 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20663
                       then
                         let uu____20668 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20670 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20668 uu____20670
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20716 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20716
            then
              let uu____20721 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20723 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20725 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20727 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20721 uu____20723 uu____20725 uu____20727
            else ());
           (let uu____20732 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20732 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20763,uu____20764) ->
                     let rec may_relate head =
                       let uu____20792 =
                         let uu____20793 = FStar_Syntax_Subst.compress head
                            in
                         uu____20793.FStar_Syntax_Syntax.n  in
                       match uu____20792 with
                       | FStar_Syntax_Syntax.Tm_name uu____20797 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20799 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20824 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20824 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20826 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20829
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20830 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20833,uu____20834) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20876) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20882) ->
                           may_relate t
                       | uu____20887 -> false  in
                     let uu____20889 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20889 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20902 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20902
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20912 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20912
                          then
                            let uu____20915 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20915 with
                             | (guard,wl2) ->
                                 let uu____20922 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20922)
                          else
                            (let uu____20925 =
                               mklstr
                                 (fun uu____20936  ->
                                    let uu____20937 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20939 =
                                      let uu____20941 =
                                        let uu____20945 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20945
                                          (fun x  ->
                                             let uu____20952 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20952)
                                         in
                                      FStar_Util.dflt "" uu____20941  in
                                    let uu____20957 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20959 =
                                      let uu____20961 =
                                        let uu____20965 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20965
                                          (fun x  ->
                                             let uu____20972 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20972)
                                         in
                                      FStar_Util.dflt "" uu____20961  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20937 uu____20939 uu____20957
                                      uu____20959)
                                in
                             giveup env1 uu____20925 orig))
                 | (HeadMatch (true ),uu____20978) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20993 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20993 with
                        | (guard,wl2) ->
                            let uu____21000 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____21000)
                     else
                       (let uu____21003 =
                          mklstr
                            (fun uu____21010  ->
                               let uu____21011 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____21013 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____21011 uu____21013)
                           in
                        giveup env1 uu____21003 orig)
                 | (uu____21016,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2942_21030 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2942_21030.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2942_21030.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2942_21030.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2942_21030.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2942_21030.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2942_21030.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2942_21030.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2942_21030.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____21057 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____21057
          then
            let uu____21060 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____21060
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____21066 =
                let uu____21069 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21069  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____21066 t1);
             (let uu____21088 =
                let uu____21091 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21091  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____21088 t2);
             (let uu____21110 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____21110
              then
                let uu____21114 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____21116 =
                  let uu____21118 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____21120 =
                    let uu____21122 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____21122  in
                  Prims.op_Hat uu____21118 uu____21120  in
                let uu____21125 =
                  let uu____21127 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____21129 =
                    let uu____21131 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____21131  in
                  Prims.op_Hat uu____21127 uu____21129  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21114 uu____21116 uu____21125
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21138,uu____21139) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21155,FStar_Syntax_Syntax.Tm_delayed uu____21156) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21172,uu____21173) ->
                  let uu____21200 =
                    let uu___2973_21201 = problem  in
                    let uu____21202 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2973_21201.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21202;
                      FStar_TypeChecker_Common.relation =
                        (uu___2973_21201.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2973_21201.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2973_21201.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2973_21201.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2973_21201.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2973_21201.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2973_21201.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2973_21201.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21200 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21203,uu____21204) ->
                  let uu____21211 =
                    let uu___2979_21212 = problem  in
                    let uu____21213 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2979_21212.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21213;
                      FStar_TypeChecker_Common.relation =
                        (uu___2979_21212.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2979_21212.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2979_21212.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2979_21212.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2979_21212.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2979_21212.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2979_21212.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2979_21212.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21211 wl
              | (uu____21214,FStar_Syntax_Syntax.Tm_ascribed uu____21215) ->
                  let uu____21242 =
                    let uu___2985_21243 = problem  in
                    let uu____21244 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2985_21243.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2985_21243.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2985_21243.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21244;
                      FStar_TypeChecker_Common.element =
                        (uu___2985_21243.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2985_21243.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2985_21243.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2985_21243.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2985_21243.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2985_21243.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21242 wl
              | (uu____21245,FStar_Syntax_Syntax.Tm_meta uu____21246) ->
                  let uu____21253 =
                    let uu___2991_21254 = problem  in
                    let uu____21255 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2991_21254.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2991_21254.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2991_21254.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21255;
                      FStar_TypeChecker_Common.element =
                        (uu___2991_21254.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2991_21254.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2991_21254.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2991_21254.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2991_21254.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2991_21254.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21253 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21257),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21259)) ->
                  let uu____21268 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21268
              | (FStar_Syntax_Syntax.Tm_bvar uu____21269,uu____21270) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21272,FStar_Syntax_Syntax.Tm_bvar uu____21273) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___27_21343 =
                    match uu___27_21343 with
                    | [] -> c
                    | bs ->
                        let uu____21371 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21371
                     in
                  let uu____21382 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21382 with
                   | ((bs11,c11),(bs21,c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst c21
                                     in
                                  let rel =
                                    let uu____21531 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21531
                                    then FStar_TypeChecker_Common.EQ
                                    else
                                      problem.FStar_TypeChecker_Common.relation
                                     in
                                  mk_c_problem wl1 scope orig c12 rel c22
                                    FStar_Pervasives_Native.None
                                    "function co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs
                 (bs1,tbody1,lopt1),FStar_Syntax_Syntax.Tm_abs
                 (bs2,tbody2,lopt2)) ->
                  let mk_t t l uu___28_21620 =
                    match uu___28_21620 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21662 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21662 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21807 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21808 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21807
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21808 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21810,uu____21811) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21842 -> true
                    | uu____21862 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____21922 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3093_21930 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3093_21930.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3093_21930.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3093_21930.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3093_21930.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3093_21930.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3093_21930.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3093_21930.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3093_21930.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3093_21930.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3093_21930.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3093_21930.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3093_21930.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3093_21930.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3093_21930.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3093_21930.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3093_21930.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3093_21930.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3093_21930.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3093_21930.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3093_21930.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3093_21930.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3093_21930.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3093_21930.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3093_21930.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3093_21930.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3093_21930.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3093_21930.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3093_21930.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3093_21930.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3093_21930.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3093_21930.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3093_21930.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3093_21930.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3093_21930.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3093_21930.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3093_21930.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3093_21930.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3093_21930.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3093_21930.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3093_21930.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3093_21930.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3093_21930.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3093_21930.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3093_21930.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____21922 with
                       | (uu____21935,ty,uu____21937) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21946 =
                                 let uu____21947 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21947.FStar_Syntax_Syntax.n  in
                               match uu____21946 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21950 ->
                                   let uu____21957 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21957
                               | uu____21958 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21961 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21961
                             then
                               let uu____21966 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21968 =
                                 let uu____21970 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21970
                                  in
                               let uu____21971 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21966 uu____21968 uu____21971
                             else ());
                            r1))
                     in
                  let uu____21976 =
                    let uu____21993 = maybe_eta t1  in
                    let uu____22000 = maybe_eta t2  in
                    (uu____21993, uu____22000)  in
                  (match uu____21976 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3114_22042 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3114_22042.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3114_22042.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3114_22042.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3114_22042.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3114_22042.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3114_22042.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3114_22042.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3114_22042.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22063 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22063
                       then
                         let uu____22066 = destruct_flex_t not_abs wl  in
                         (match uu____22066 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3131_22083 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3131_22083.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3131_22083.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3131_22083.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3131_22083.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3131_22083.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3131_22083.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3131_22083.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3131_22083.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22086 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22086 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22109 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22109
                       then
                         let uu____22112 = destruct_flex_t not_abs wl  in
                         (match uu____22112 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3131_22129 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3131_22129.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3131_22129.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3131_22129.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3131_22129.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3131_22129.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3131_22129.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3131_22129.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3131_22129.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22132 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22132 orig))
                   | uu____22135 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22153,FStar_Syntax_Syntax.Tm_abs uu____22154) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22185 -> true
                    | uu____22205 -> false  in
                  let maybe_eta t =
                    if is_abs t
                    then FStar_Util.Inl t
                    else
                      (let t3 =
                         FStar_TypeChecker_Normalize.eta_expand wl.tcenv t
                          in
                       if is_abs t3
                       then FStar_Util.Inl t3
                       else FStar_Util.Inr t3)
                     in
                  let force_eta t =
                    if is_abs t
                    then t
                    else
                      (let uu____22265 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3093_22273 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3093_22273.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3093_22273.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3093_22273.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3093_22273.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3093_22273.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3093_22273.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3093_22273.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3093_22273.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3093_22273.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3093_22273.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3093_22273.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3093_22273.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3093_22273.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3093_22273.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3093_22273.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3093_22273.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3093_22273.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3093_22273.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3093_22273.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3093_22273.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3093_22273.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3093_22273.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3093_22273.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3093_22273.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3093_22273.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3093_22273.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3093_22273.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3093_22273.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3093_22273.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3093_22273.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3093_22273.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3093_22273.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3093_22273.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3093_22273.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3093_22273.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3093_22273.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3093_22273.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3093_22273.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3093_22273.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3093_22273.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3093_22273.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3093_22273.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3093_22273.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3093_22273.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____22265 with
                       | (uu____22278,ty,uu____22280) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22289 =
                                 let uu____22290 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22290.FStar_Syntax_Syntax.n  in
                               match uu____22289 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22293 ->
                                   let uu____22300 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22300
                               | uu____22301 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22304 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22304
                             then
                               let uu____22309 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22311 =
                                 let uu____22313 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22313
                                  in
                               let uu____22314 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22309 uu____22311 uu____22314
                             else ());
                            r1))
                     in
                  let uu____22319 =
                    let uu____22336 = maybe_eta t1  in
                    let uu____22343 = maybe_eta t2  in
                    (uu____22336, uu____22343)  in
                  (match uu____22319 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3114_22385 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3114_22385.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3114_22385.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3114_22385.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3114_22385.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3114_22385.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3114_22385.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3114_22385.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3114_22385.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22406 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22406
                       then
                         let uu____22409 = destruct_flex_t not_abs wl  in
                         (match uu____22409 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3131_22426 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3131_22426.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3131_22426.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3131_22426.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3131_22426.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3131_22426.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3131_22426.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3131_22426.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3131_22426.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22429 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22429 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22452 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22452
                       then
                         let uu____22455 = destruct_flex_t not_abs wl  in
                         (match uu____22455 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3131_22472 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3131_22472.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3131_22472.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3131_22472.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3131_22472.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3131_22472.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3131_22472.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3131_22472.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3131_22472.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22475 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22475 orig))
                   | uu____22478 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22508 =
                    let uu____22513 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22513 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3154_22541 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3154_22541.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3154_22541.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3156_22543 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3156_22543.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3156_22543.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22544,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3154_22559 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3154_22559.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3154_22559.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3156_22561 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3156_22561.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3156_22561.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22562 -> (x1, x2)  in
                  (match uu____22508 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22581 = as_refinement false env t11  in
                       (match uu____22581 with
                        | (x12,phi11) ->
                            let uu____22589 = as_refinement false env t21  in
                            (match uu____22589 with
                             | (x22,phi21) ->
                                 ((let uu____22598 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22598
                                   then
                                     ((let uu____22603 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22605 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22607 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22603
                                         uu____22605 uu____22607);
                                      (let uu____22610 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22612 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22614 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22610
                                         uu____22612 uu____22614))
                                   else ());
                                  (let uu____22619 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22619 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)]
                                          in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst phi11
                                          in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst phi21
                                          in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13
                                          in
                                       let mk_imp imp phi13 phi23 =
                                         let uu____22690 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22690
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22702 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp FStar_Syntax_Util.mk_imp
                                               phi12 phi22
                                            in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         (let uu____22715 =
                                            let uu____22718 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22718
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22715
                                            (p_guard base_prob));
                                         (let uu____22737 =
                                            let uu____22740 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22740
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22737
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22759 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22759)
                                          in
                                       let has_uvars =
                                         (let uu____22764 =
                                            let uu____22766 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22766
                                             in
                                          Prims.op_Negation uu____22764) ||
                                           (let uu____22770 =
                                              let uu____22772 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22772
                                               in
                                            Prims.op_Negation uu____22770)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22776 =
                                           let uu____22781 =
                                             let uu____22790 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22790]  in
                                           mk_t_problem wl1 uu____22781 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22776 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22813 =
                                                solve env1
                                                  (let uu___3199_22815 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3199_22815.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3199_22815.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3199_22815.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3199_22815.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3199_22815.tcenv);
                                                     wl_implicits =
                                                       (uu___3199_22815.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3199_22815.repr_subcomp_allowed)
                                                   })
                                                 in
                                              (match uu____22813 with
                                               | Failed (prob,msg) ->
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
                                                   (uu____22830,defer_to_tac,uu____22832)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22837 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22837
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3215_22846 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3215_22846.attempting);
                                                         wl_deferred =
                                                           (uu___3215_22846.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3215_22846.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3215_22846.defer_ok);
                                                         smt_ok =
                                                           (uu___3215_22846.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3215_22846.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3215_22846.tcenv);
                                                         wl_implicits =
                                                           (uu___3215_22846.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3215_22846.repr_subcomp_allowed)
                                                       }  in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac []
                                                        in
                                                     let uu____22849 =
                                                       attempt [base_prob]
                                                         wl5
                                                        in
                                                     solve env1 uu____22849))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22852,FStar_Syntax_Syntax.Tm_uvar uu____22853) ->
                  let uu____22878 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22878 with
                   | (t11,wl1) ->
                       let uu____22885 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22885 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22894;
                    FStar_Syntax_Syntax.pos = uu____22895;
                    FStar_Syntax_Syntax.vars = uu____22896;_},uu____22897),FStar_Syntax_Syntax.Tm_uvar
                 uu____22898) ->
                  let uu____22947 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22947 with
                   | (t11,wl1) ->
                       let uu____22954 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22954 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22963,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22964;
                    FStar_Syntax_Syntax.pos = uu____22965;
                    FStar_Syntax_Syntax.vars = uu____22966;_},uu____22967))
                  ->
                  let uu____23016 = ensure_no_uvar_subst t1 wl  in
                  (match uu____23016 with
                   | (t11,wl1) ->
                       let uu____23023 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____23023 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23032;
                    FStar_Syntax_Syntax.pos = uu____23033;
                    FStar_Syntax_Syntax.vars = uu____23034;_},uu____23035),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23036;
                    FStar_Syntax_Syntax.pos = uu____23037;
                    FStar_Syntax_Syntax.vars = uu____23038;_},uu____23039))
                  ->
                  let uu____23112 = ensure_no_uvar_subst t1 wl  in
                  (match uu____23112 with
                   | (t11,wl1) ->
                       let uu____23119 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____23119 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23128,uu____23129) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23142 = destruct_flex_t t1 wl  in
                  (match uu____23142 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23149;
                    FStar_Syntax_Syntax.pos = uu____23150;
                    FStar_Syntax_Syntax.vars = uu____23151;_},uu____23152),uu____23153)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23190 = destruct_flex_t t1 wl  in
                  (match uu____23190 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23197,FStar_Syntax_Syntax.Tm_uvar uu____23198) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23211,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23212;
                    FStar_Syntax_Syntax.pos = uu____23213;
                    FStar_Syntax_Syntax.vars = uu____23214;_},uu____23215))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23252,FStar_Syntax_Syntax.Tm_arrow uu____23253) ->
                  solve_t' env
                    (let uu___3318_23281 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3318_23281.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3318_23281.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3318_23281.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3318_23281.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3318_23281.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3318_23281.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3318_23281.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3318_23281.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3318_23281.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23282;
                    FStar_Syntax_Syntax.pos = uu____23283;
                    FStar_Syntax_Syntax.vars = uu____23284;_},uu____23285),FStar_Syntax_Syntax.Tm_arrow
                 uu____23286) ->
                  solve_t' env
                    (let uu___3318_23338 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3318_23338.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3318_23338.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3318_23338.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3318_23338.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3318_23338.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3318_23338.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3318_23338.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3318_23338.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3318_23338.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23339,FStar_Syntax_Syntax.Tm_uvar uu____23340) ->
                  let uu____23353 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23353
              | (uu____23354,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23355;
                    FStar_Syntax_Syntax.pos = uu____23356;
                    FStar_Syntax_Syntax.vars = uu____23357;_},uu____23358))
                  ->
                  let uu____23395 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23395
              | (FStar_Syntax_Syntax.Tm_uvar uu____23396,uu____23397) ->
                  let uu____23410 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23410
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23411;
                    FStar_Syntax_Syntax.pos = uu____23412;
                    FStar_Syntax_Syntax.vars = uu____23413;_},uu____23414),uu____23415)
                  ->
                  let uu____23452 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23452
              | (FStar_Syntax_Syntax.Tm_refine uu____23453,uu____23454) ->
                  let t21 =
                    let uu____23462 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23462  in
                  solve_t env
                    (let uu___3353_23488 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3353_23488.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3353_23488.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3353_23488.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3353_23488.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3353_23488.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3353_23488.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3353_23488.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3353_23488.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3353_23488.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23489,FStar_Syntax_Syntax.Tm_refine uu____23490) ->
                  let t11 =
                    let uu____23498 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23498  in
                  solve_t env
                    (let uu___3360_23524 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3360_23524.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3360_23524.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3360_23524.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3360_23524.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3360_23524.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3360_23524.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3360_23524.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3360_23524.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3360_23524.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23606 =
                    let uu____23607 = guard_of_prob env wl problem t1 t2  in
                    match uu____23607 with
                    | (guard,wl1) ->
                        let uu____23614 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23614
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23833 = br1  in
                        (match uu____23833 with
                         | (p1,w1,uu____23862) ->
                             let uu____23879 = br2  in
                             (match uu____23879 with
                              | (p2,w2,uu____23902) ->
                                  let uu____23907 =
                                    let uu____23909 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23909  in
                                  if uu____23907
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23936 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23936 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23973 = br2  in
                                         (match uu____23973 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____24006 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____24006
                                                 in
                                              let uu____24011 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____24042,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____24063) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____24122 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____24122 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____24011
                                                (fun uu____24194  ->
                                                   match uu____24194 with
                                                   | (wprobs,wl2) ->
                                                       let uu____24231 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____24231
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24252
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24252
                                                              then
                                                                let uu____24257
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24259
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24257
                                                                  uu____24259
                                                              else ());
                                                             (let uu____24265
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24265
                                                                (fun
                                                                   uu____24301
                                                                    ->
                                                                   match uu____24301
                                                                   with
                                                                   | 
                                                                   (r1,wl4)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (((scope,
                                                                    prob) ::
                                                                    (FStar_List.append
                                                                    wprobs r1)),
                                                                    wl4))))))))))
                    | ([],[]) -> FStar_Pervasives_Native.Some ([], wl1)
                    | uu____24430 -> FStar_Pervasives_Native.None  in
                  let uu____24471 = solve_branches wl brs1 brs2  in
                  (match uu____24471 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24497 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24497 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24524 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24524 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24558 =
                                FStar_List.map
                                  (fun uu____24570  ->
                                     match uu____24570 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24558  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24579 =
                              let uu____24580 =
                                let uu____24581 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24581
                                  (let uu___3459_24589 = wl3  in
                                   {
                                     attempting =
                                       (uu___3459_24589.attempting);
                                     wl_deferred =
                                       (uu___3459_24589.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3459_24589.wl_deferred_to_tac);
                                     ctr = (uu___3459_24589.ctr);
                                     defer_ok = (uu___3459_24589.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3459_24589.umax_heuristic_ok);
                                     tcenv = (uu___3459_24589.tcenv);
                                     wl_implicits =
                                       (uu___3459_24589.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3459_24589.repr_subcomp_allowed)
                                   })
                                 in
                              solve env uu____24580  in
                            (match uu____24579 with
                             | Success (ds,ds',imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24595 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24604 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24604 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24607,uu____24608) ->
                  let head1 =
                    let uu____24632 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24632
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24678 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24678
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24724 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24724
                    then
                      let uu____24728 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24730 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24732 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24728 uu____24730 uu____24732
                    else ());
                   (let no_free_uvars t =
                      (let uu____24746 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24746) &&
                        (let uu____24750 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24750)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24769 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24769 = FStar_Syntax_Util.Equal  in
                    let uu____24770 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24770
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24774 = equal t1 t2  in
                         (if uu____24774
                          then
                            let uu____24777 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24777
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24782 =
                            let uu____24789 = equal t1 t2  in
                            if uu____24789
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24802 = mk_eq2 wl env orig t1 t2  in
                               match uu____24802 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24782 with
                          | (guard,wl1) ->
                              let uu____24823 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24823))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24826,uu____24827) ->
                  let head1 =
                    let uu____24835 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24835
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24881 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24881
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24927 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24927
                    then
                      let uu____24931 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24933 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24935 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24931 uu____24933 uu____24935
                    else ());
                   (let no_free_uvars t =
                      (let uu____24949 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24949) &&
                        (let uu____24953 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24953)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____24972 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24972 = FStar_Syntax_Util.Equal  in
                    let uu____24973 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24973
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24977 = equal t1 t2  in
                         (if uu____24977
                          then
                            let uu____24980 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24980
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24985 =
                            let uu____24992 = equal t1 t2  in
                            if uu____24992
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25005 = mk_eq2 wl env orig t1 t2  in
                               match uu____25005 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24985 with
                          | (guard,wl1) ->
                              let uu____25026 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25026))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____25029,uu____25030) ->
                  let head1 =
                    let uu____25032 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25032
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25078 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25078
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25124 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25124
                    then
                      let uu____25128 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25130 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25132 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25128 uu____25130 uu____25132
                    else ());
                   (let no_free_uvars t =
                      (let uu____25146 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25146) &&
                        (let uu____25150 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25150)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25169 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25169 = FStar_Syntax_Util.Equal  in
                    let uu____25170 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25170
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25174 = equal t1 t2  in
                         (if uu____25174
                          then
                            let uu____25177 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25177
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25182 =
                            let uu____25189 = equal t1 t2  in
                            if uu____25189
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25202 = mk_eq2 wl env orig t1 t2  in
                               match uu____25202 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25182 with
                          | (guard,wl1) ->
                              let uu____25223 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25223))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25226,uu____25227) ->
                  let head1 =
                    let uu____25229 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25229
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25275 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25275
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25321 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25321
                    then
                      let uu____25325 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25327 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25329 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25325 uu____25327 uu____25329
                    else ());
                   (let no_free_uvars t =
                      (let uu____25343 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25343) &&
                        (let uu____25347 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25347)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25366 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25366 = FStar_Syntax_Util.Equal  in
                    let uu____25367 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25367
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25371 = equal t1 t2  in
                         (if uu____25371
                          then
                            let uu____25374 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25374
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25379 =
                            let uu____25386 = equal t1 t2  in
                            if uu____25386
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25399 = mk_eq2 wl env orig t1 t2  in
                               match uu____25399 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25379 with
                          | (guard,wl1) ->
                              let uu____25420 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25420))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25423,uu____25424) ->
                  let head1 =
                    let uu____25426 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25426
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25466 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25466
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25506 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25506
                    then
                      let uu____25510 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25512 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25514 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25510 uu____25512 uu____25514
                    else ());
                   (let no_free_uvars t =
                      (let uu____25528 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25528) &&
                        (let uu____25532 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25532)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25551 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25551 = FStar_Syntax_Util.Equal  in
                    let uu____25552 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25552
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25556 = equal t1 t2  in
                         (if uu____25556
                          then
                            let uu____25559 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25559
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25564 =
                            let uu____25571 = equal t1 t2  in
                            if uu____25571
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25584 = mk_eq2 wl env orig t1 t2  in
                               match uu____25584 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25564 with
                          | (guard,wl1) ->
                              let uu____25605 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25605))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25608,uu____25609) ->
                  let head1 =
                    let uu____25627 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25627
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25667 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25667
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25707 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25707
                    then
                      let uu____25711 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25713 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25715 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25711 uu____25713 uu____25715
                    else ());
                   (let no_free_uvars t =
                      (let uu____25729 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25729) &&
                        (let uu____25733 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25733)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25752 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25752 = FStar_Syntax_Util.Equal  in
                    let uu____25753 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25753
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25757 = equal t1 t2  in
                         (if uu____25757
                          then
                            let uu____25760 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25760
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25765 =
                            let uu____25772 = equal t1 t2  in
                            if uu____25772
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25785 = mk_eq2 wl env orig t1 t2  in
                               match uu____25785 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25765 with
                          | (guard,wl1) ->
                              let uu____25806 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25806))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25809,FStar_Syntax_Syntax.Tm_match uu____25810) ->
                  let head1 =
                    let uu____25834 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25834
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25874 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25874
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25914 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25914
                    then
                      let uu____25918 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25920 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25922 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25918 uu____25920 uu____25922
                    else ());
                   (let no_free_uvars t =
                      (let uu____25936 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25936) &&
                        (let uu____25940 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25940)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____25959 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25959 = FStar_Syntax_Util.Equal  in
                    let uu____25960 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25960
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25964 = equal t1 t2  in
                         (if uu____25964
                          then
                            let uu____25967 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25967
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25972 =
                            let uu____25979 = equal t1 t2  in
                            if uu____25979
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25992 = mk_eq2 wl env orig t1 t2  in
                               match uu____25992 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25972 with
                          | (guard,wl1) ->
                              let uu____26013 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26013))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26016,FStar_Syntax_Syntax.Tm_uinst uu____26017) ->
                  let head1 =
                    let uu____26025 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26025
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26065 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26065
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26105 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26105
                    then
                      let uu____26109 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26111 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26113 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26109 uu____26111 uu____26113
                    else ());
                   (let no_free_uvars t =
                      (let uu____26127 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26127) &&
                        (let uu____26131 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26131)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26150 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26150 = FStar_Syntax_Util.Equal  in
                    let uu____26151 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26151
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26155 = equal t1 t2  in
                         (if uu____26155
                          then
                            let uu____26158 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26158
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26163 =
                            let uu____26170 = equal t1 t2  in
                            if uu____26170
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26183 = mk_eq2 wl env orig t1 t2  in
                               match uu____26183 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26163 with
                          | (guard,wl1) ->
                              let uu____26204 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26204))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26207,FStar_Syntax_Syntax.Tm_name uu____26208) ->
                  let head1 =
                    let uu____26210 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26210
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26250 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26250
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26290 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26290
                    then
                      let uu____26294 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26296 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26298 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26294 uu____26296 uu____26298
                    else ());
                   (let no_free_uvars t =
                      (let uu____26312 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26312) &&
                        (let uu____26316 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26316)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26335 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26335 = FStar_Syntax_Util.Equal  in
                    let uu____26336 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26336
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26340 = equal t1 t2  in
                         (if uu____26340
                          then
                            let uu____26343 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26343
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26348 =
                            let uu____26355 = equal t1 t2  in
                            if uu____26355
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26368 = mk_eq2 wl env orig t1 t2  in
                               match uu____26368 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26348 with
                          | (guard,wl1) ->
                              let uu____26389 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26389))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26392,FStar_Syntax_Syntax.Tm_constant uu____26393) ->
                  let head1 =
                    let uu____26395 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26395
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26435 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26435
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26475 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26475
                    then
                      let uu____26479 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26481 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26483 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26479 uu____26481 uu____26483
                    else ());
                   (let no_free_uvars t =
                      (let uu____26497 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26497) &&
                        (let uu____26501 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26501)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26520 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26520 = FStar_Syntax_Util.Equal  in
                    let uu____26521 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26521
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26525 = equal t1 t2  in
                         (if uu____26525
                          then
                            let uu____26528 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26528
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26533 =
                            let uu____26540 = equal t1 t2  in
                            if uu____26540
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26553 = mk_eq2 wl env orig t1 t2  in
                               match uu____26553 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26533 with
                          | (guard,wl1) ->
                              let uu____26574 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26574))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26577,FStar_Syntax_Syntax.Tm_fvar uu____26578) ->
                  let head1 =
                    let uu____26580 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26580
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26626 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26626
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26672 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26672
                    then
                      let uu____26676 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26678 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26680 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26676 uu____26678 uu____26680
                    else ());
                   (let no_free_uvars t =
                      (let uu____26694 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26694) &&
                        (let uu____26698 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26698)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26717 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26717 = FStar_Syntax_Util.Equal  in
                    let uu____26718 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26718
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26722 = equal t1 t2  in
                         (if uu____26722
                          then
                            let uu____26725 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26725
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26730 =
                            let uu____26737 = equal t1 t2  in
                            if uu____26737
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26750 = mk_eq2 wl env orig t1 t2  in
                               match uu____26750 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26730 with
                          | (guard,wl1) ->
                              let uu____26771 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26771))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26774,FStar_Syntax_Syntax.Tm_app uu____26775) ->
                  let head1 =
                    let uu____26793 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26793
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26833 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26833
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26873 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26873
                    then
                      let uu____26877 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26879 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26881 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26877 uu____26879 uu____26881
                    else ());
                   (let no_free_uvars t =
                      (let uu____26895 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26895) &&
                        (let uu____26899 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26899)
                       in
                    let equal t11 t21 =
                      let t12 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.2"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t11
                         in
                      let t22 =
                        norm_with_steps
                          "FStar.TypeChecker.Rel.norm_with_steps.3"
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.Beta;
                          FStar_TypeChecker_Env.Eager_unfolding;
                          FStar_TypeChecker_Env.Iota] env t21
                         in
                      let uu____26918 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26918 = FStar_Syntax_Util.Equal  in
                    let uu____26919 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26919
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26923 = equal t1 t2  in
                         (if uu____26923
                          then
                            let uu____26926 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26926
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26931 =
                            let uu____26938 = equal t1 t2  in
                            if uu____26938
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26951 = mk_eq2 wl env orig t1 t2  in
                               match uu____26951 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26931 with
                          | (guard,wl1) ->
                              let uu____26972 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26972))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26975,FStar_Syntax_Syntax.Tm_let uu____26976) ->
                  let uu____27003 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____27003
                  then
                    let uu____27006 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____27006
                  else
                    (let uu____27009 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____27009 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____27012,uu____27013) ->
                  let uu____27027 =
                    let uu____27033 =
                      let uu____27035 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____27037 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____27039 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____27041 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27035 uu____27037 uu____27039 uu____27041
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27033)
                     in
                  FStar_Errors.raise_error uu____27027
                    t1.FStar_Syntax_Syntax.pos
              | (uu____27045,FStar_Syntax_Syntax.Tm_let uu____27046) ->
                  let uu____27060 =
                    let uu____27066 =
                      let uu____27068 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____27070 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____27072 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____27074 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27068 uu____27070 uu____27072 uu____27074
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27066)
                     in
                  FStar_Errors.raise_error uu____27060
                    t1.FStar_Syntax_Syntax.pos
              | uu____27078 ->
                  let uu____27083 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____27083 orig))))

and (solve_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem ->
      worklist -> solution)
  =
  fun env  ->
    fun problem  ->
      fun wl  ->
        let c1 = problem.FStar_TypeChecker_Common.lhs  in
        let c2 = problem.FStar_TypeChecker_Common.rhs  in
        let orig = FStar_TypeChecker_Common.CProb problem  in
        let sub_prob wl1 t1 rel t2 reason =
          mk_t_problem wl1 [] orig t1 rel t2 FStar_Pervasives_Native.None
            reason
           in
        let solve_eq c1_comp c2_comp g_lift =
          (let uu____27149 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____27149
           then
             let uu____27154 =
               let uu____27156 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____27156  in
             let uu____27157 =
               let uu____27159 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____27159  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27154 uu____27157
           else ());
          (let uu____27163 =
             let uu____27165 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____27165  in
           if uu____27163
           then
             let uu____27168 =
               mklstr
                 (fun uu____27175  ->
                    let uu____27176 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____27178 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27176 uu____27178)
                in
             giveup env uu____27168 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27200 =
                  mklstr
                    (fun uu____27207  ->
                       let uu____27208 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27210 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27208 uu____27210)
                   in
                giveup env uu____27200 orig)
             else
               (let uu____27215 =
                  FStar_List.fold_left2
                    (fun uu____27236  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27236 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27257 =
                                 let uu____27262 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27263 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27262
                                   FStar_TypeChecker_Common.EQ uu____27263
                                   "effect universes"
                                  in
                               (match uu____27257 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27215 with
                | (univ_sub_probs,wl1) ->
                    let uu____27283 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27283 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27291 =
                           FStar_List.fold_right2
                             (fun uu____27328  ->
                                fun uu____27329  ->
                                  fun uu____27330  ->
                                    match (uu____27328, uu____27329,
                                            uu____27330)
                                    with
                                    | ((a1,uu____27374),(a2,uu____27376),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27409 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27409 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27291 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27436 =
                                  let uu____27439 =
                                    let uu____27442 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27442
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27439
                                   in
                                FStar_List.append univ_sub_probs uu____27436
                                 in
                              let guard =
                                let guard =
                                  let uu____27464 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27464  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3612_27473 = wl3  in
                                {
                                  attempting = (uu___3612_27473.attempting);
                                  wl_deferred = (uu___3612_27473.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3612_27473.wl_deferred_to_tac);
                                  ctr = (uu___3612_27473.ctr);
                                  defer_ok = (uu___3612_27473.defer_ok);
                                  smt_ok = (uu___3612_27473.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3612_27473.umax_heuristic_ok);
                                  tcenv = (uu___3612_27473.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3612_27473.repr_subcomp_allowed)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27475 = attempt sub_probs wl5  in
                              solve env uu____27475))))
           in
        let solve_layered_sub c11 c21 =
          (let uu____27488 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsApp")
              in
           if uu____27488
           then
             let uu____27493 =
               let uu____27495 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27495
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27497 =
               let uu____27499 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27499
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27493 uu____27497
           else ());
          if
            problem.FStar_TypeChecker_Common.relation =
              FStar_TypeChecker_Common.EQ
          then solve_eq c11 c21 FStar_TypeChecker_Env.trivial_guard
          else
            (let r = FStar_TypeChecker_Env.get_range env  in
             let subcomp_name =
               let uu____27510 =
                 let uu____27512 =
                   FStar_All.pipe_right c11.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid
                    in
                 FStar_All.pipe_right uu____27512 FStar_Ident.string_of_id
                  in
               let uu____27514 =
                 let uu____27516 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.effect_name
                     FStar_Ident.ident_of_lid
                    in
                 FStar_All.pipe_right uu____27516 FStar_Ident.string_of_id
                  in
               FStar_Util.format2 "%s <: %s" uu____27510 uu____27514  in
             let lift_c1 edge =
               let uu____27533 =
                 let uu____27538 =
                   FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
                 FStar_All.pipe_right uu____27538
                   ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                      env)
                  in
               FStar_All.pipe_right uu____27533
                 (fun uu____27555  ->
                    match uu____27555 with
                    | (c,g) ->
                        let uu____27566 =
                          FStar_Syntax_Util.comp_to_comp_typ c  in
                        (uu____27566, g))
                in
             let uu____27567 =
               let uu____27579 =
                 FStar_TypeChecker_Env.exists_polymonadic_subcomp env
                   c11.FStar_Syntax_Syntax.effect_name
                   c21.FStar_Syntax_Syntax.effect_name
                  in
               match uu____27579 with
               | FStar_Pervasives_Native.None  ->
                   let uu____27593 =
                     FStar_TypeChecker_Env.monad_leq env
                       c11.FStar_Syntax_Syntax.effect_name
                       c21.FStar_Syntax_Syntax.effect_name
                      in
                   (match uu____27593 with
                    | FStar_Pervasives_Native.None  ->
                        (c11, FStar_TypeChecker_Env.trivial_guard,
                          FStar_Pervasives_Native.None, false)
                    | FStar_Pervasives_Native.Some edge ->
                        let uu____27612 = lift_c1 edge  in
                        (match uu____27612 with
                         | (c12,g_lift) ->
                             let uu____27630 =
                               let uu____27633 =
                                 let uu____27634 =
                                   FStar_All.pipe_right
                                     c21.FStar_Syntax_Syntax.effect_name
                                     (FStar_TypeChecker_Env.get_effect_decl
                                        env)
                                    in
                                 FStar_All.pipe_right uu____27634
                                   FStar_Syntax_Util.get_stronger_vc_combinator
                                  in
                               FStar_All.pipe_right uu____27633
                                 (fun ts  ->
                                    let uu____27640 =
                                      let uu____27641 =
                                        FStar_TypeChecker_Env.inst_tscheme_with
                                          ts
                                          c21.FStar_Syntax_Syntax.comp_univs
                                         in
                                      FStar_All.pipe_right uu____27641
                                        FStar_Pervasives_Native.snd
                                       in
                                    FStar_All.pipe_right uu____27640
                                      (fun uu____27652  ->
                                         FStar_Pervasives_Native.Some
                                           uu____27652))
                                in
                             (c12, g_lift, uu____27630, false)))
               | FStar_Pervasives_Native.Some t ->
                   let uu____27658 =
                     let uu____27661 =
                       let uu____27662 =
                         FStar_TypeChecker_Env.inst_tscheme_with t
                           c21.FStar_Syntax_Syntax.comp_univs
                          in
                       FStar_All.pipe_right uu____27662
                         FStar_Pervasives_Native.snd
                        in
                     FStar_All.pipe_right uu____27661
                       (fun uu____27673  ->
                          FStar_Pervasives_Native.Some uu____27673)
                      in
                   (c11, FStar_TypeChecker_Env.trivial_guard, uu____27658,
                     true)
                in
             match uu____27567 with
             | (c12,g_lift,stronger_t_opt,is_polymonadic) ->
                 if FStar_Util.is_none stronger_t_opt
                 then
                   let uu____27689 =
                     mklstr
                       (fun uu____27696  ->
                          let uu____27697 =
                            FStar_Syntax_Print.lid_to_string
                              c12.FStar_Syntax_Syntax.effect_name
                             in
                          let uu____27699 =
                            FStar_Syntax_Print.lid_to_string
                              c21.FStar_Syntax_Syntax.effect_name
                             in
                          FStar_Util.format2
                            "incompatible monad ordering: %s </: %s"
                            uu____27697 uu____27699)
                      in
                   giveup env uu____27689 orig
                 else
                   (let stronger_t =
                      FStar_All.pipe_right stronger_t_opt FStar_Util.must  in
                    let wl1 =
                      let uu___3647_27708 = wl  in
                      {
                        attempting = (uu___3647_27708.attempting);
                        wl_deferred = (uu___3647_27708.wl_deferred);
                        wl_deferred_to_tac =
                          (uu___3647_27708.wl_deferred_to_tac);
                        ctr = (uu___3647_27708.ctr);
                        defer_ok = (uu___3647_27708.defer_ok);
                        smt_ok = (uu___3647_27708.smt_ok);
                        umax_heuristic_ok =
                          (uu___3647_27708.umax_heuristic_ok);
                        tcenv = (uu___3647_27708.tcenv);
                        wl_implicits =
                          (FStar_List.append
                             g_lift.FStar_TypeChecker_Common.implicits
                             wl.wl_implicits);
                        repr_subcomp_allowed =
                          (uu___3647_27708.repr_subcomp_allowed)
                      }  in
                    let uu____27709 =
                      if is_polymonadic
                      then ([], wl1)
                      else
                        (let rec is_uvar t =
                           let uu____27734 =
                             let uu____27735 = FStar_Syntax_Subst.compress t
                                in
                             uu____27735.FStar_Syntax_Syntax.n  in
                           match uu____27734 with
                           | FStar_Syntax_Syntax.Tm_uvar uu____27739 -> true
                           | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27754) ->
                               is_uvar t1
                           | FStar_Syntax_Syntax.Tm_app (t1,uu____27760) ->
                               is_uvar t1
                           | uu____27785 -> false  in
                         FStar_List.fold_right2
                           (fun uu____27819  ->
                              fun uu____27820  ->
                                fun uu____27821  ->
                                  match (uu____27819, uu____27820,
                                          uu____27821)
                                  with
                                  | ((a1,uu____27865),(a2,uu____27867),
                                     (is_sub_probs,wl2)) ->
                                      let uu____27900 = is_uvar a1  in
                                      if uu____27900
                                      then
                                        ((let uu____27910 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsEqns")
                                             in
                                          if uu____27910
                                          then
                                            let uu____27915 =
                                              FStar_Syntax_Print.term_to_string
                                                a1
                                               in
                                            let uu____27917 =
                                              FStar_Syntax_Print.term_to_string
                                                a2
                                               in
                                            FStar_Util.print2
                                              "Layered Effects teq (rel c1 index uvar) %s = %s\n"
                                              uu____27915 uu____27917
                                          else ());
                                         (let uu____27922 =
                                            sub_prob wl2 a1
                                              FStar_TypeChecker_Common.EQ a2
                                              "l.h.s. effect index uvar"
                                             in
                                          match uu____27922 with
                                          | (p,wl3) ->
                                              ((p :: is_sub_probs), wl3)))
                                      else (is_sub_probs, wl2))
                           c12.FStar_Syntax_Syntax.effect_args
                           c21.FStar_Syntax_Syntax.effect_args ([], wl1))
                       in
                    match uu____27709 with
                    | (is_sub_probs,wl2) ->
                        let uu____27950 =
                          sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                            problem.FStar_TypeChecker_Common.relation
                            c21.FStar_Syntax_Syntax.result_typ "result type"
                           in
                        (match uu____27950 with
                         | (ret_sub_prob,wl3) ->
                             let stronger_t_shape_error s =
                               let uu____27967 =
                                 FStar_Ident.string_of_lid
                                   c21.FStar_Syntax_Syntax.effect_name
                                  in
                               let uu____27969 =
                                 FStar_Syntax_Print.term_to_string stronger_t
                                  in
                               FStar_Util.format3
                                 "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                 uu____27967 s uu____27969
                                in
                             let uu____27972 =
                               let uu____28001 =
                                 let uu____28002 =
                                   FStar_Syntax_Subst.compress stronger_t  in
                                 uu____28002.FStar_Syntax_Syntax.n  in
                               match uu____28001 with
                               | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                   (FStar_List.length bs) >=
                                     (Prims.of_int (2))
                                   ->
                                   let uu____28062 =
                                     FStar_Syntax_Subst.open_comp bs c  in
                                   (match uu____28062 with
                                    | (bs',c3) ->
                                        let a = FStar_List.hd bs'  in
                                        let bs1 = FStar_List.tail bs'  in
                                        let uu____28125 =
                                          let uu____28144 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.splitAt
                                                 ((FStar_List.length bs1) -
                                                    Prims.int_one))
                                             in
                                          FStar_All.pipe_right uu____28144
                                            (fun uu____28248  ->
                                               match uu____28248 with
                                               | (l1,l2) ->
                                                   let uu____28321 =
                                                     FStar_List.hd l2  in
                                                   (l1, uu____28321))
                                           in
                                        (match uu____28125 with
                                         | (rest_bs,f_b) ->
                                             (a, rest_bs, f_b, c3)))
                               | uu____28426 ->
                                   let uu____28427 =
                                     let uu____28433 =
                                       stronger_t_shape_error
                                         "not an arrow or not enough binders"
                                        in
                                     (FStar_Errors.Fatal_UnexpectedExpressionType,
                                       uu____28433)
                                      in
                                   FStar_Errors.raise_error uu____28427 r
                                in
                             (match uu____27972 with
                              | (a_b,rest_bs,f_b,stronger_c) ->
                                  let uu____28509 =
                                    let uu____28516 =
                                      let uu____28517 =
                                        let uu____28518 =
                                          let uu____28525 =
                                            FStar_All.pipe_right a_b
                                              FStar_Pervasives_Native.fst
                                             in
                                          (uu____28525,
                                            (c21.FStar_Syntax_Syntax.result_typ))
                                           in
                                        FStar_Syntax_Syntax.NT uu____28518
                                         in
                                      [uu____28517]  in
                                    FStar_TypeChecker_Env.uvars_for_binders
                                      env rest_bs uu____28516
                                      (fun b  ->
                                         let uu____28541 =
                                           FStar_Syntax_Print.binder_to_string
                                             b
                                            in
                                         let uu____28543 =
                                           FStar_Ident.string_of_lid
                                             c21.FStar_Syntax_Syntax.effect_name
                                            in
                                         let uu____28545 =
                                           FStar_Range.string_of_range r  in
                                         FStar_Util.format3
                                           "implicit for binder %s in subcomp of %s at %s"
                                           uu____28541 uu____28543
                                           uu____28545) r
                                     in
                                  (match uu____28509 with
                                   | (rest_bs_uvars,g_uvars) ->
                                       let wl4 =
                                         let uu___3712_28555 = wl3  in
                                         {
                                           attempting =
                                             (uu___3712_28555.attempting);
                                           wl_deferred =
                                             (uu___3712_28555.wl_deferred);
                                           wl_deferred_to_tac =
                                             (uu___3712_28555.wl_deferred_to_tac);
                                           ctr = (uu___3712_28555.ctr);
                                           defer_ok =
                                             (uu___3712_28555.defer_ok);
                                           smt_ok = (uu___3712_28555.smt_ok);
                                           umax_heuristic_ok =
                                             (uu___3712_28555.umax_heuristic_ok);
                                           tcenv = (uu___3712_28555.tcenv);
                                           wl_implicits =
                                             (FStar_List.append
                                                g_uvars.FStar_TypeChecker_Common.implicits
                                                wl3.wl_implicits);
                                           repr_subcomp_allowed =
                                             (uu___3712_28555.repr_subcomp_allowed)
                                         }  in
                                       let substs =
                                         FStar_List.map2
                                           (fun b  ->
                                              fun t  ->
                                                let uu____28580 =
                                                  let uu____28587 =
                                                    FStar_All.pipe_right b
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  (uu____28587, t)  in
                                                FStar_Syntax_Syntax.NT
                                                  uu____28580) (a_b ::
                                           rest_bs)
                                           ((c21.FStar_Syntax_Syntax.result_typ)
                                           :: rest_bs_uvars)
                                          in
                                       let uu____28604 =
                                         let f_sort_is =
                                           let uu____28614 =
                                             let uu____28617 =
                                               let uu____28618 =
                                                 FStar_All.pipe_right f_b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               uu____28618.FStar_Syntax_Syntax.sort
                                                in
                                             let uu____28627 =
                                               FStar_TypeChecker_Env.is_layered_effect
                                                 env
                                                 c12.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28629 =
                                               stronger_t_shape_error
                                                 "type of f is not a repr type"
                                                in
                                             FStar_Syntax_Util.effect_indices_from_repr
                                               uu____28617 uu____28627 r
                                               uu____28629
                                              in
                                           FStar_All.pipe_right uu____28614
                                             (FStar_List.map
                                                (FStar_Syntax_Subst.subst
                                                   substs))
                                            in
                                         let uu____28636 =
                                           FStar_All.pipe_right
                                             c12.FStar_Syntax_Syntax.effect_args
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst)
                                            in
                                         FStar_List.fold_left2
                                           (fun uu____28672  ->
                                              fun f_sort_i  ->
                                                fun c1_i  ->
                                                  match uu____28672 with
                                                  | (ps,wl5) ->
                                                      ((let uu____28694 =
                                                          FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffectsEqns")
                                                           in
                                                        if uu____28694
                                                        then
                                                          let uu____28699 =
                                                            FStar_Syntax_Print.term_to_string
                                                              f_sort_i
                                                             in
                                                          let uu____28701 =
                                                            FStar_Syntax_Print.term_to_string
                                                              c1_i
                                                             in
                                                          FStar_Util.print3
                                                            "Layered Effects (%s) %s = %s\n"
                                                            subcomp_name
                                                            uu____28699
                                                            uu____28701
                                                        else ());
                                                       (let uu____28706 =
                                                          sub_prob wl5
                                                            f_sort_i
                                                            FStar_TypeChecker_Common.EQ
                                                            c1_i
                                                            "indices of c1"
                                                           in
                                                        match uu____28706
                                                        with
                                                        | (p,wl6) ->
                                                            ((FStar_List.append
                                                                ps [p]), wl6))))
                                           ([], wl4) f_sort_is uu____28636
                                          in
                                       (match uu____28604 with
                                        | (f_sub_probs,wl5) ->
                                            let stronger_ct =
                                              let uu____28731 =
                                                FStar_All.pipe_right
                                                  stronger_c
                                                  (FStar_Syntax_Subst.subst_comp
                                                     substs)
                                                 in
                                              FStar_All.pipe_right
                                                uu____28731
                                                FStar_Syntax_Util.comp_to_comp_typ
                                               in
                                            let uu____28732 =
                                              let g_sort_is =
                                                let uu____28742 =
                                                  FStar_TypeChecker_Env.is_layered_effect
                                                    env
                                                    c21.FStar_Syntax_Syntax.effect_name
                                                   in
                                                let uu____28744 =
                                                  stronger_t_shape_error
                                                    "subcomp return type is not a repr"
                                                   in
                                                FStar_Syntax_Util.effect_indices_from_repr
                                                  stronger_ct.FStar_Syntax_Syntax.result_typ
                                                  uu____28742 r uu____28744
                                                 in
                                              let uu____28747 =
                                                FStar_All.pipe_right
                                                  c21.FStar_Syntax_Syntax.effect_args
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst)
                                                 in
                                              FStar_List.fold_left2
                                                (fun uu____28783  ->
                                                   fun g_sort_i  ->
                                                     fun c2_i  ->
                                                       match uu____28783 with
                                                       | (ps,wl6) ->
                                                           ((let uu____28805
                                                               =
                                                               FStar_All.pipe_left
                                                                 (FStar_TypeChecker_Env.debug
                                                                    env)
                                                                 (FStar_Options.Other
                                                                    "LayeredEffectsEqns")
                                                                in
                                                             if uu____28805
                                                             then
                                                               let uu____28810
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   g_sort_i
                                                                  in
                                                               let uu____28812
                                                                 =
                                                                 FStar_Syntax_Print.term_to_string
                                                                   c2_i
                                                                  in
                                                               FStar_Util.print3
                                                                 "Layered Effects (%s) %s = %s\n"
                                                                 subcomp_name
                                                                 uu____28810
                                                                 uu____28812
                                                             else ());
                                                            (let uu____28817
                                                               =
                                                               sub_prob wl6
                                                                 g_sort_i
                                                                 FStar_TypeChecker_Common.EQ
                                                                 c2_i
                                                                 "indices of c2"
                                                                in
                                                             match uu____28817
                                                             with
                                                             | (p,wl7) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl7))))
                                                ([], wl5) g_sort_is
                                                uu____28747
                                               in
                                            (match uu____28732 with
                                             | (g_sub_probs,wl6) ->
                                                 let fml =
                                                   let uu____28844 =
                                                     let uu____28849 =
                                                       FStar_List.hd
                                                         stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                        in
                                                     let uu____28850 =
                                                       let uu____28851 =
                                                         FStar_List.hd
                                                           stronger_ct.FStar_Syntax_Syntax.effect_args
                                                          in
                                                       FStar_Pervasives_Native.fst
                                                         uu____28851
                                                        in
                                                     (uu____28849,
                                                       uu____28850)
                                                      in
                                                   match uu____28844 with
                                                   | (u,wp) ->
                                                       FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                         env u
                                                         stronger_ct.FStar_Syntax_Syntax.result_typ
                                                         wp
                                                         FStar_Range.dummyRange
                                                    in
                                                 let sub_probs =
                                                   let uu____28879 =
                                                     let uu____28882 =
                                                       let uu____28885 =
                                                         let uu____28888 =
                                                           FStar_All.pipe_right
                                                             g_lift.FStar_TypeChecker_Common.deferred
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         FStar_List.append
                                                           g_sub_probs
                                                           uu____28888
                                                          in
                                                       FStar_List.append
                                                         f_sub_probs
                                                         uu____28885
                                                        in
                                                     FStar_List.append
                                                       is_sub_probs
                                                       uu____28882
                                                      in
                                                   ret_sub_prob ::
                                                     uu____28879
                                                    in
                                                 let guard =
                                                   let guard =
                                                     let uu____28912 =
                                                       FStar_List.map p_guard
                                                         sub_probs
                                                        in
                                                     FStar_Syntax_Util.mk_conj_l
                                                       uu____28912
                                                      in
                                                   match g_lift.FStar_TypeChecker_Common.guard_f
                                                   with
                                                   | FStar_TypeChecker_Common.Trivial
                                                        -> guard
                                                   | FStar_TypeChecker_Common.NonTrivial
                                                       f ->
                                                       FStar_Syntax_Util.mk_conj
                                                         guard f
                                                    in
                                                 let wl7 =
                                                   let uu____28923 =
                                                     let uu____28926 =
                                                       FStar_Syntax_Util.mk_conj
                                                         guard fml
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun uu____28929  ->
                                                          FStar_Pervasives_Native.Some
                                                            uu____28929)
                                                       uu____28926
                                                      in
                                                   solve_prob orig
                                                     uu____28923 [] wl6
                                                    in
                                                 let uu____28930 =
                                                   attempt sub_probs wl7  in
                                                 solve env uu____28930)))))))
           in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env  in
           let lift_c1 uu____28958 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____28960 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ
                      in
                   [uu____28960]
               | x -> x  in
             let c12 =
               let uu___3770_28963 = c11  in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3770_28963.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3770_28963.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3770_28963.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3770_28963.FStar_Syntax_Syntax.flags)
               }  in
             let uu____28964 =
               let uu____28969 =
                 FStar_All.pipe_right
                   (let uu___3773_28971 = c12  in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3773_28971.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3773_28971.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3773_28971.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3773_28971.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____28969
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____28964
               (fun uu____28985  ->
                  match uu____28985 with
                  | (c,g) ->
                      let uu____28992 =
                        let uu____28994 = FStar_TypeChecker_Env.is_trivial g
                           in
                        Prims.op_Negation uu____28994  in
                      if uu____28992
                      then
                        let uu____28997 =
                          let uu____29003 =
                            let uu____29005 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name
                               in
                            let uu____29007 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name
                               in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____29005 uu____29007
                             in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____29003)
                           in
                        FStar_Errors.raise_error uu____28997 r
                      else FStar_Syntax_Util.comp_to_comp_typ c)
              in
           let uu____29013 =
             ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                (let uu____29016 =
                   FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
                     c21.FStar_Syntax_Syntax.effect_name
                    in
                 Prims.op_Negation uu____29016))
               &&
               (FStar_TypeChecker_Env.is_reifiable_effect env
                  c21.FStar_Syntax_Syntax.effect_name)
              in
           if uu____29013
           then
             let uu____29019 =
               mklstr
                 (fun uu____29026  ->
                    let uu____29027 =
                      FStar_Ident.string_of_lid
                        c11.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____29029 =
                      FStar_Ident.string_of_lid
                        c21.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2
                      "Cannot lift from %s to %s, it needs a lift\n"
                      uu____29027 uu____29029)
                in
             giveup env uu____29019 orig
           else
             (let is_null_wp_2 =
                FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                  (FStar_Util.for_some
                     (fun uu___29_29040  ->
                        match uu___29_29040 with
                        | FStar_Syntax_Syntax.TOTAL  -> true
                        | FStar_Syntax_Syntax.MLEFFECT  -> true
                        | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                        | uu____29045 -> false))
                 in
              let uu____29047 =
                match ((c11.FStar_Syntax_Syntax.effect_args),
                        (c21.FStar_Syntax_Syntax.effect_args))
                with
                | ((wp1,uu____29077)::uu____29078,(wp2,uu____29080)::uu____29081)
                    -> (wp1, wp2)
                | uu____29154 ->
                    let uu____29179 =
                      let uu____29185 =
                        let uu____29187 =
                          FStar_Syntax_Print.lid_to_string
                            c11.FStar_Syntax_Syntax.effect_name
                           in
                        let uu____29189 =
                          FStar_Syntax_Print.lid_to_string
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.format2
                          "Got effects %s and %s, expected normalized effects"
                          uu____29187 uu____29189
                         in
                      (FStar_Errors.Fatal_ExpectNormalizedEffect,
                        uu____29185)
                       in
                    FStar_Errors.raise_error uu____29179
                      env.FStar_TypeChecker_Env.range
                 in
              match uu____29047 with
              | (wpc1,wpc2) ->
                  let uu____29199 = FStar_Util.physical_equality wpc1 wpc2
                     in
                  if uu____29199
                  then
                    let uu____29202 =
                      problem_using_guard orig
                        c11.FStar_Syntax_Syntax.result_typ
                        problem.FStar_TypeChecker_Common.relation
                        c21.FStar_Syntax_Syntax.result_typ
                        FStar_Pervasives_Native.None "result type"
                       in
                    solve_t env uu____29202 wl
                  else
                    (let uu____29206 =
                       let uu____29213 =
                         FStar_TypeChecker_Env.effect_decl_opt env
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.must uu____29213  in
                     match uu____29206 with
                     | (c2_decl,qualifiers) ->
                         let uu____29234 =
                           FStar_All.pipe_right qualifiers
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Reifiable)
                            in
                         if uu____29234
                         then
                           let c1_repr =
                             let uu____29241 =
                               let uu____29242 =
                                 let uu____29243 = lift_c1 ()  in
                                 FStar_Syntax_Syntax.mk_Comp uu____29243  in
                               let uu____29244 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c11.FStar_Syntax_Syntax.result_typ
                                  in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____29242 uu____29244
                                in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.4"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____29241
                              in
                           let c2_repr =
                             let uu____29247 =
                               let uu____29248 =
                                 FStar_Syntax_Syntax.mk_Comp c21  in
                               let uu____29249 =
                                 env.FStar_TypeChecker_Env.universe_of env
                                   c21.FStar_Syntax_Syntax.result_typ
                                  in
                               FStar_TypeChecker_Env.reify_comp env
                                 uu____29248 uu____29249
                                in
                             norm_with_steps
                               "FStar.TypeChecker.Rel.norm_with_steps.5"
                               [FStar_TypeChecker_Env.UnfoldUntil
                                  FStar_Syntax_Syntax.delta_constant;
                               FStar_TypeChecker_Env.Weak;
                               FStar_TypeChecker_Env.HNF] env uu____29247
                              in
                           let uu____29251 =
                             let uu____29256 =
                               let uu____29258 =
                                 FStar_Syntax_Print.term_to_string c1_repr
                                  in
                               let uu____29260 =
                                 FStar_Syntax_Print.term_to_string c2_repr
                                  in
                               FStar_Util.format2 "sub effect repr: %s <: %s"
                                 uu____29258 uu____29260
                                in
                             sub_prob wl c1_repr
                               problem.FStar_TypeChecker_Common.relation
                               c2_repr uu____29256
                              in
                           (match uu____29251 with
                            | (prob,wl1) ->
                                let wl2 =
                                  solve_prob orig
                                    (FStar_Pervasives_Native.Some
                                       (p_guard prob)) [] wl1
                                   in
                                let uu____29266 = attempt [prob] wl2  in
                                solve env uu____29266)
                         else
                           (let g =
                              if env.FStar_TypeChecker_Env.lax
                              then FStar_Syntax_Util.t_true
                              else
                                (let wpc1_2 =
                                   let uu____29286 = lift_c1 ()  in
                                   FStar_All.pipe_right uu____29286
                                     (fun ct  ->
                                        FStar_List.hd
                                          ct.FStar_Syntax_Syntax.effect_args)
                                    in
                                 if is_null_wp_2
                                 then
                                   ((let uu____29309 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____29309
                                     then
                                       FStar_Util.print_string
                                         "Using trivial wp ... \n"
                                     else ());
                                    (let c1_univ =
                                       env.FStar_TypeChecker_Env.universe_of
                                         env
                                         c11.FStar_Syntax_Syntax.result_typ
                                        in
                                     let trivial =
                                       let uu____29319 =
                                         FStar_All.pipe_right c2_decl
                                           FStar_Syntax_Util.get_wp_trivial_combinator
                                          in
                                       match uu____29319 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "Rel doesn't yet handle undefined trivial combinator in an effect"
                                       | FStar_Pervasives_Native.Some t -> t
                                        in
                                     let uu____29326 =
                                       let uu____29327 =
                                         let uu____29344 =
                                           FStar_TypeChecker_Env.inst_effect_fun_with
                                             [c1_univ] env c2_decl trivial
                                            in
                                         let uu____29347 =
                                           let uu____29358 =
                                             FStar_Syntax_Syntax.as_arg
                                               c11.FStar_Syntax_Syntax.result_typ
                                              in
                                           [uu____29358; wpc1_2]  in
                                         (uu____29344, uu____29347)  in
                                       FStar_Syntax_Syntax.Tm_app uu____29327
                                        in
                                     FStar_Syntax_Syntax.mk uu____29326 r))
                                 else
                                   (let c2_univ =
                                      env.FStar_TypeChecker_Env.universe_of
                                        env
                                        c21.FStar_Syntax_Syntax.result_typ
                                       in
                                    let stronger =
                                      FStar_All.pipe_right c2_decl
                                        FStar_Syntax_Util.get_stronger_vc_combinator
                                       in
                                    let uu____29407 =
                                      let uu____29408 =
                                        let uu____29425 =
                                          FStar_TypeChecker_Env.inst_effect_fun_with
                                            [c2_univ] env c2_decl stronger
                                           in
                                        let uu____29428 =
                                          let uu____29439 =
                                            FStar_Syntax_Syntax.as_arg
                                              c21.FStar_Syntax_Syntax.result_typ
                                             in
                                          let uu____29448 =
                                            let uu____29459 =
                                              FStar_Syntax_Syntax.as_arg wpc2
                                               in
                                            [uu____29459; wpc1_2]  in
                                          uu____29439 :: uu____29448  in
                                        (uu____29425, uu____29428)  in
                                      FStar_Syntax_Syntax.Tm_app uu____29408
                                       in
                                    FStar_Syntax_Syntax.mk uu____29407 r))
                               in
                            (let uu____29513 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____29513
                             then
                               let uu____29518 =
                                 let uu____29520 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Env.Iota;
                                     FStar_TypeChecker_Env.Eager_unfolding;
                                     FStar_TypeChecker_Env.Primops;
                                     FStar_TypeChecker_Env.Simplify] env g
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____29520
                                  in
                               FStar_Util.print1
                                 "WP guard (simplifed) is (%s)\n" uu____29518
                             else ());
                            (let uu____29524 =
                               sub_prob wl c11.FStar_Syntax_Syntax.result_typ
                                 problem.FStar_TypeChecker_Common.relation
                                 c21.FStar_Syntax_Syntax.result_typ
                                 "result type"
                                in
                             match uu____29524 with
                             | (base_prob,wl1) ->
                                 let wl2 =
                                   let uu____29533 =
                                     let uu____29536 =
                                       FStar_Syntax_Util.mk_conj
                                         (p_guard base_prob) g
                                        in
                                     FStar_All.pipe_left
                                       (fun uu____29539  ->
                                          FStar_Pervasives_Native.Some
                                            uu____29539) uu____29536
                                      in
                                   solve_prob orig uu____29533 [] wl1  in
                                 let uu____29540 = attempt [base_prob] wl2
                                    in
                                 solve env uu____29540)))))
           in
        let uu____29541 = FStar_Util.physical_equality c1 c2  in
        if uu____29541
        then
          let uu____29544 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29544
        else
          ((let uu____29548 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29548
            then
              let uu____29553 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29555 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29553
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29555
            else ());
           (let uu____29560 =
              let uu____29569 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29572 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29569, uu____29572)  in
            match uu____29560 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29590),FStar_Syntax_Syntax.Total
                    (t2,uu____29592)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29609 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29609 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29611,FStar_Syntax_Syntax.Total uu____29612) ->
                     let uu____29629 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29629 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29633),FStar_Syntax_Syntax.Total
                    (t2,uu____29635)) ->
                     let uu____29652 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29652 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29655),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29657)) ->
                     let uu____29674 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29674 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29677),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29679)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29696 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29696 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29699),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29701)) ->
                     let uu____29718 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29718 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29721,FStar_Syntax_Syntax.Comp uu____29722) ->
                     let uu____29731 =
                       let uu___3897_29734 = problem  in
                       let uu____29737 =
                         let uu____29738 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29738
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3897_29734.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29737;
                         FStar_TypeChecker_Common.relation =
                           (uu___3897_29734.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3897_29734.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3897_29734.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3897_29734.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3897_29734.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3897_29734.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3897_29734.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3897_29734.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29731 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29739,FStar_Syntax_Syntax.Comp uu____29740) ->
                     let uu____29749 =
                       let uu___3897_29752 = problem  in
                       let uu____29755 =
                         let uu____29756 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29756
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3897_29752.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29755;
                         FStar_TypeChecker_Common.relation =
                           (uu___3897_29752.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3897_29752.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3897_29752.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3897_29752.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3897_29752.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3897_29752.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3897_29752.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3897_29752.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29749 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29757,FStar_Syntax_Syntax.GTotal uu____29758) ->
                     let uu____29767 =
                       let uu___3909_29770 = problem  in
                       let uu____29773 =
                         let uu____29774 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29774
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3909_29770.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3909_29770.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3909_29770.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29773;
                         FStar_TypeChecker_Common.element =
                           (uu___3909_29770.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3909_29770.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3909_29770.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3909_29770.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3909_29770.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3909_29770.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29767 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29775,FStar_Syntax_Syntax.Total uu____29776) ->
                     let uu____29785 =
                       let uu___3909_29788 = problem  in
                       let uu____29791 =
                         let uu____29792 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29792
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3909_29788.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3909_29788.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3909_29788.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29791;
                         FStar_TypeChecker_Common.element =
                           (uu___3909_29788.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3909_29788.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3909_29788.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3909_29788.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3909_29788.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3909_29788.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29785 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29793,FStar_Syntax_Syntax.Comp uu____29794) ->
                     let uu____29795 =
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
                               FStar_TypeChecker_Common.SUB))
                        in
                     if uu____29795
                     then
                       let uu____29798 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29798 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29805 =
                            let uu____29810 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29810
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29819 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29820 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29819, uu____29820))
                             in
                          match uu____29805 with
                          | (c1_comp1,c2_comp1) ->
                              solve_eq c1_comp1 c2_comp1
                                FStar_TypeChecker_Env.trivial_guard
                        else
                          (let c12 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c11
                              in
                           let c22 =
                             FStar_TypeChecker_Env.unfold_effect_abbrev env
                               c21
                              in
                           (let uu____29828 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29828
                            then
                              let uu____29833 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29835 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29833 uu____29835
                            else ());
                           (let uu____29840 =
                              FStar_TypeChecker_Env.is_layered_effect env
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29840
                            then solve_layered_sub c12 c22
                            else
                              (let uu____29845 =
                                 FStar_TypeChecker_Env.monad_leq env
                                   c12.FStar_Syntax_Syntax.effect_name
                                   c22.FStar_Syntax_Syntax.effect_name
                                  in
                               match uu____29845 with
                               | FStar_Pervasives_Native.None  ->
                                   let uu____29848 =
                                     mklstr
                                       (fun uu____29855  ->
                                          let uu____29856 =
                                            FStar_Syntax_Print.lid_to_string
                                              c12.FStar_Syntax_Syntax.effect_name
                                             in
                                          let uu____29858 =
                                            FStar_Syntax_Print.lid_to_string
                                              c22.FStar_Syntax_Syntax.effect_name
                                             in
                                          FStar_Util.format2
                                            "incompatible monad ordering: %s </: %s"
                                            uu____29856 uu____29858)
                                      in
                                   giveup env uu____29848 orig
                               | FStar_Pervasives_Native.Some edge ->
                                   solve_sub c12 edge c22)))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29869 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29869 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29919 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29919 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29944 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29975  ->
                match uu____29975 with
                | (u1,u2) ->
                    let uu____29983 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29985 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29983 uu____29985))
         in
      FStar_All.pipe_right uu____29944 (FStar_String.concat ", ")  in
    FStar_Util.format2 "Solving for {%s}; inequalities are {%s}" vars ineqs1
  
let (guard_to_string :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> Prims.string)
  =
  fun env  ->
    fun g  ->
      match ((g.FStar_TypeChecker_Common.guard_f),
              (g.FStar_TypeChecker_Common.deferred),
              (g.FStar_TypeChecker_Common.univ_ineqs))
      with
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____30022,[])) when
          let uu____30049 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____30049 -> "{}"
      | uu____30052 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____30079 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____30079
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry defs =
            let uu____30110 =
              FStar_List.map
                (fun uu____30124  ->
                   match uu____30124 with
                   | (msg,x) ->
                       let uu____30135 =
                         let uu____30137 = prob_to_string env x  in
                         Prims.op_Hat ": " uu____30137  in
                       Prims.op_Hat msg uu____30135) defs
               in
            FStar_All.pipe_right uu____30110 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30147 = carry g.FStar_TypeChecker_Common.deferred  in
          let uu____30149 = carry g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____30151 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30147 uu____30149 uu____30151 imps
  
let (new_t_problem :
  worklist ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_TypeChecker_Common.rel ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
              FStar_Range.range -> (FStar_TypeChecker_Common.prob * worklist))
  =
  fun wl  ->
    fun env  ->
      fun lhs  ->
        fun rel  ->
          fun rhs  ->
            fun elt  ->
              fun loc  ->
                let reason =
                  let uu____30208 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30208
                  then
                    let uu____30216 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30218 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30216
                      (rel_to_string rel) uu____30218
                  else "TOP"  in
                let uu____30224 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30224 with
                | (p,wl1) ->
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
  fun wl  ->
    fun env  ->
      fun t1  ->
        fun rel  ->
          fun t2  ->
            let x =
              let uu____30284 =
                let uu____30287 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____30290  ->
                     FStar_Pervasives_Native.Some uu____30290) uu____30287
                 in
              FStar_Syntax_Syntax.new_bv uu____30284 t1  in
            let uu____30291 =
              let uu____30296 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30296
               in
            match uu____30291 with | (p,wl1) -> (p, x, wl1)
  
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
  fun env  ->
    fun probs  ->
      fun err  ->
        let tx = FStar_Syntax_Unionfind.new_transaction ()  in
        (let uu____30368 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30368
         then
           let uu____30373 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30373
         else ());
        (let uu____30380 =
           FStar_Util.record_time (fun uu____30387  -> solve env probs)  in
         match uu____30380 with
         | (sol,ms) ->
             ((let uu____30401 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30401
               then
                 let uu____30406 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30406
               else ());
              (match sol with
               | Success (deferred,defer_to_tac,implicits) ->
                   let uu____30422 =
                     FStar_Util.record_time
                       (fun uu____30429  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30422 with
                    | ((),ms1) ->
                        ((let uu____30442 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30442
                          then
                            let uu____30447 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30447
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d,s) ->
                   ((let uu____30461 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30461
                     then
                       let uu____30468 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30468
                     else ());
                    (let result = err (d, s)  in
                     FStar_Syntax_Unionfind.rollback tx; result)))))
  
let (simplify_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      match g.FStar_TypeChecker_Common.guard_f with
      | FStar_TypeChecker_Common.Trivial  -> g
      | FStar_TypeChecker_Common.NonTrivial f ->
          ((let uu____30496 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30496
            then
              let uu____30501 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30501
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30509 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30509
             then
               let uu____30514 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30514
             else ());
            (let f2 =
               let uu____30520 =
                 let uu____30521 = FStar_Syntax_Util.unmeta f1  in
                 uu____30521.FStar_Syntax_Syntax.n  in
               match uu____30520 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30525 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4029_30526 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4029_30526.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4029_30526.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4029_30526.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4029_30526.FStar_TypeChecker_Common.implicits)
             })))
  
let (with_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred
        * FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
        -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,defer_to_tac,implicits) ->
            let uu____30578 =
              let uu____30579 =
                let uu____30580 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30581  ->
                       FStar_TypeChecker_Common.NonTrivial uu____30581)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30580;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30579  in
            FStar_All.pipe_left
              (fun uu____30588  -> FStar_Pervasives_Native.Some uu____30588)
              uu____30578
  
let with_guard_no_simp :
  'uuuuuu30598 .
    'uuuuuu30598 ->
      FStar_TypeChecker_Common.prob ->
        (FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.deferred *
          FStar_TypeChecker_Common.implicits) FStar_Pervasives_Native.option
          -> FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
  =
  fun env  ->
    fun prob  ->
      fun dopt  ->
        match dopt with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (deferred,defer_to_tac,implicits) ->
            let uu____30647 =
              let uu____30648 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30649  ->
                     FStar_TypeChecker_Common.NonTrivial uu____30649)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30648;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30647
  
let (try_teq :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.typ ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun smt_ok  ->
    fun env  ->
      fun t1  ->
        fun t2  ->
          (let uu____30682 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30682
           then
             let uu____30687 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30689 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30687
               uu____30689
           else ());
          (let uu____30694 =
             let uu____30699 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30699
              in
           match uu____30694 with
           | (prob,wl) ->
               let g =
                 let uu____30707 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30717  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30707  in
               ((let uu____30739 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30739
                 then
                   let uu____30744 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30744
                 else ());
                g))
  
let (teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____30765 = try_teq true env t1 t2  in
        match uu____30765 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30770 = FStar_TypeChecker_Env.get_range env  in
              let uu____30771 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30770 uu____30771);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30779 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30779
              then
                let uu____30784 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30786 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30788 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30784
                  uu____30786 uu____30788
              else ());
             g)
  
let (get_teq_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____30812 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30812
         then
           let uu____30817 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30819 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30817
             uu____30819
         else ());
        (let uu____30824 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30824 with
         | (prob,x,wl) ->
             let g =
               let uu____30839 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30850  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30839  in
             ((let uu____30872 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30872
               then
                 let uu____30877 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30877
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30885 =
                     let uu____30886 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30886 g1  in
                   FStar_Pervasives_Native.Some uu____30885)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30908 = FStar_TypeChecker_Env.get_range env  in
          let uu____30909 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30908 uu____30909
  
let (sub_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun c1  ->
      fun c2  ->
        let rel =
          if env.FStar_TypeChecker_Env.use_eq
          then FStar_TypeChecker_Common.EQ
          else FStar_TypeChecker_Common.SUB  in
        (let uu____30938 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30938
         then
           let uu____30943 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30945 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30943 uu____30945
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30956 =
           let uu____30963 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30963 "sub_comp"
            in
         match uu____30956 with
         | (prob,wl) ->
             let wl1 =
               let uu___4102_30974 = wl  in
               {
                 attempting = (uu___4102_30974.attempting);
                 wl_deferred = (uu___4102_30974.wl_deferred);
                 wl_deferred_to_tac = (uu___4102_30974.wl_deferred_to_tac);
                 ctr = (uu___4102_30974.ctr);
                 defer_ok = (uu___4102_30974.defer_ok);
                 smt_ok = (uu___4102_30974.smt_ok);
                 umax_heuristic_ok = (uu___4102_30974.umax_heuristic_ok);
                 tcenv = (uu___4102_30974.tcenv);
                 wl_implicits = (uu___4102_30974.wl_implicits);
                 repr_subcomp_allowed = true
               }  in
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30979 =
                 FStar_Util.record_time
                   (fun uu____30991  ->
                      let uu____30992 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____31003  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30992)
                  in
               match uu____30979 with
               | (r,ms) ->
                   ((let uu____31035 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____31035
                     then
                       let uu____31040 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____31042 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____31044 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____31040 uu____31042
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____31044
                     else ());
                    r))))
  
let (solve_universe_inequalities' :
  FStar_Syntax_Unionfind.tx ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.universe Prims.list *
        (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe)
        Prims.list) -> unit)
  =
  fun tx  ->
    fun env  ->
      fun uu____31082  ->
        match uu____31082 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31125 =
                 let uu____31131 =
                   let uu____31133 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31135 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31133 uu____31135
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31131)  in
               let uu____31139 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31125 uu____31139)
               in
            let equiv v v' =
              let uu____31152 =
                let uu____31157 = FStar_Syntax_Subst.compress_univ v  in
                let uu____31158 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31157, uu____31158)  in
              match uu____31152 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31182 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____31213 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____31213 with
                      | FStar_Syntax_Syntax.U_unif uu____31220 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31251  ->
                                    match uu____31251 with
                                    | (u,v') ->
                                        let uu____31260 = equiv v v'  in
                                        if uu____31260
                                        then
                                          let uu____31265 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____31265 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____31286 -> []))
               in
            let uu____31291 =
              let wl =
                let uu___4145_31295 = empty_worklist env  in
                {
                  attempting = (uu___4145_31295.attempting);
                  wl_deferred = (uu___4145_31295.wl_deferred);
                  wl_deferred_to_tac = (uu___4145_31295.wl_deferred_to_tac);
                  ctr = (uu___4145_31295.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4145_31295.smt_ok);
                  umax_heuristic_ok = (uu___4145_31295.umax_heuristic_ok);
                  tcenv = (uu___4145_31295.tcenv);
                  wl_implicits = (uu___4145_31295.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4145_31295.repr_subcomp_allowed)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31314  ->
                      match uu____31314 with
                      | (lb,v) ->
                          let uu____31321 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____31321 with
                           | USolved wl1 -> ()
                           | uu____31324 -> fail lb v)))
               in
            let rec check_ineq uu____31335 =
              match uu____31335 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31347) -> true
                   | (FStar_Syntax_Syntax.U_succ
                      u0,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u0, v0)
                   | (FStar_Syntax_Syntax.U_name
                      u0,FStar_Syntax_Syntax.U_name v0) ->
                       FStar_Ident.ident_equals u0 v0
                   | (FStar_Syntax_Syntax.U_unif
                      u0,FStar_Syntax_Syntax.U_unif v0) ->
                       FStar_Syntax_Unionfind.univ_equiv u0 v0
                   | (FStar_Syntax_Syntax.U_name
                      uu____31375,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31377,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31390) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____31398,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____31407 -> false)
               in
            let uu____31413 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31430  ->
                      match uu____31430 with
                      | (u,v) ->
                          let uu____31438 = check_ineq (u, v)  in
                          if uu____31438
                          then true
                          else
                            ((let uu____31446 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31446
                              then
                                let uu____31451 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31453 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____31451
                                  uu____31453
                              else ());
                             false)))
               in
            if uu____31413
            then ()
            else
              ((let uu____31463 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31463
                then
                  ((let uu____31469 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31469);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31481 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31481))
                else ());
               (let uu____31494 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31494))
  
let (solve_universe_inequalities :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe
      * FStar_Syntax_Syntax.universe) Prims.list) -> unit)
  =
  fun env  ->
    fun ineqs  ->
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      solve_universe_inequalities' tx env ineqs;
      FStar_Syntax_Unionfind.commit tx
  
let (try_solve_deferred_constraints :
  Prims.bool ->
    Prims.bool ->
      FStar_TypeChecker_Env.env ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok  ->
    fun smt_ok  ->
      fun env  ->
        fun g  ->
          let fail uu____31576 =
            match uu____31576 with
            | (d,s) ->
                let msg = explain env d s  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d)
             in
          let wl =
            let uu___4223_31603 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
            {
              attempting = (uu___4223_31603.attempting);
              wl_deferred = (uu___4223_31603.wl_deferred);
              wl_deferred_to_tac = (uu___4223_31603.wl_deferred_to_tac);
              ctr = (uu___4223_31603.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4223_31603.umax_heuristic_ok);
              tcenv = (uu___4223_31603.tcenv);
              wl_implicits = (uu___4223_31603.wl_implicits);
              repr_subcomp_allowed = (uu___4223_31603.repr_subcomp_allowed)
            }  in
          (let uu____31606 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____31606
           then
             let uu____31611 = FStar_Util.string_of_bool defer_ok  in
             let uu____31613 = wl_to_string wl  in
             let uu____31615 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits)
                in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31611 uu____31613 uu____31615
           else ());
          (let g1 =
             let uu____31621 = solve_and_commit env wl fail  in
             match uu____31621 with
             | FStar_Pervasives_Native.Some
                 (uu____31630::uu____31631,uu____31632,uu____31633) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred,defer_to_tac,imps) ->
                 let uu___4240_31667 = g  in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4240_31667.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4240_31667.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31673 ->
                 failwith "Impossible: should have raised a failure already"
              in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let g2 =
              FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
                env g1
               in
            (let uu____31686 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "ResolveImplicitsHook")
                in
             if uu____31686
             then
               let uu____31691 = guard_to_string env g2  in
               FStar_Util.print1
                 "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
                 uu____31691
             else ());
            (let uu___4248_31696 = g2  in
             {
               FStar_TypeChecker_Common.guard_f =
                 (uu___4248_31696.FStar_TypeChecker_Common.guard_f);
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4248_31696.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4248_31696.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs = ([], []);
               FStar_TypeChecker_Common.implicits =
                 (uu___4248_31696.FStar_TypeChecker_Common.implicits)
             })))
  
let (solve_deferred_constraints' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun smt_ok  ->
    fun env  -> fun g  -> try_solve_deferred_constraints false smt_ok env g
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> solve_deferred_constraints' true env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true true env g 
let (discharge_guard' :
  (unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t ->
        Prims.bool ->
          FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun use_env_range_msg  ->
    fun env  ->
      fun g  ->
        fun use_smt  ->
          let debug =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          (let uu____31792 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____31792
           then
             let uu____31797 = guard_to_string env g  in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31797
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g  in
           let ret_g =
             let uu___4265_31804 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4265_31804.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4265_31804.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4265_31804.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4265_31804.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31805 =
             let uu____31807 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31807  in
           if uu____31805
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____31819 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31820 =
                        let uu____31822 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31822
                         in
                      FStar_Errors.diag uu____31819 uu____31820)
                   else ();
                   (let vc1 =
                      let uu____31828 =
                        let uu____31832 =
                          let uu____31834 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31834  in
                        FStar_Pervasives_Native.Some uu____31832  in
                      FStar_Profiling.profile
                        (fun uu____31837  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31828 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug
                    then
                      (let uu____31841 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31842 =
                         let uu____31844 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31844
                          in
                       FStar_Errors.diag uu____31841 uu____31842)
                    else ();
                    (let uu____31850 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31850 "discharge_guard'" env vc1);
                    (let uu____31852 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31852 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____31861 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31862 =
                                 let uu____31864 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31864
                                  in
                               FStar_Errors.diag uu____31861 uu____31862)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____31874 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31875 =
                                 let uu____31877 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31877
                                  in
                               FStar_Errors.diag uu____31874 uu____31875)
                            else ();
                            (let vcs =
                               let uu____31891 = FStar_Options.use_tactics ()
                                  in
                               if uu____31891
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31913  ->
                                      (let uu____31915 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left
                                         (fun uu____31917  -> ()) uu____31915);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31960  ->
                                               match uu____31960 with
                                               | (env1,goal,opts) ->
                                                   let uu____31976 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____31976, opts)))))
                               else
                                 (let uu____31980 =
                                    let uu____31987 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____31987)  in
                                  [uu____31980])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____32020  ->
                                     match uu____32020 with
                                     | (env1,goal,opts) ->
                                         let uu____32030 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____32030 with
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
                                                 (let uu____32041 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____32042 =
                                                    let uu____32044 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____32046 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____32044 uu____32046
                                                     in
                                                  FStar_Errors.diag
                                                    uu____32041 uu____32042)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____32053 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____32054 =
                                                    let uu____32056 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____32056
                                                     in
                                                  FStar_Errors.diag
                                                    uu____32053 uu____32054)
                                               else ();
                                               (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve
                                                 use_env_range_msg env1 goal1;
                                               FStar_Options.pop ())))));
                            FStar_Pervasives_Native.Some ret_g))))))
  
let (discharge_guard_no_smt :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____32074 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____32074 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____32083 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____32083
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____32097 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____32097 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          failwith
            "Impossible, with use_smt = true, discharge_guard' should never have returned None"
  
let (teq_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32127 = try_teq false env t1 t2  in
        match uu____32127 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
let (try_solve_single_valued_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Env.implicits ->
      (FStar_TypeChecker_Env.implicits * Prims.bool))
  =
  fun env  ->
    fun imps  ->
      let imp_value imp =
        let uu____32170 =
          ((imp.FStar_TypeChecker_Common.imp_uvar),
            (imp.FStar_TypeChecker_Common.imp_range))
           in
        match uu____32170 with
        | (ctx_u,r) ->
            let t_norm =
              FStar_TypeChecker_Normalize.normalize
                FStar_TypeChecker_Normalize.whnf_steps env
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            let uu____32180 =
              let uu____32181 = FStar_Syntax_Subst.compress t_norm  in
              uu____32181.FStar_Syntax_Syntax.n  in
            (match uu____32180 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid
                 ->
                 let uu____32187 =
                   FStar_All.pipe_right r
                     FStar_Syntax_Syntax.unit_const_with_range
                    in
                 FStar_All.pipe_right uu____32187
                   (fun uu____32190  ->
                      FStar_Pervasives_Native.Some uu____32190)
             | FStar_Syntax_Syntax.Tm_refine (b,uu____32192) when
                 FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                 let uu____32197 =
                   FStar_All.pipe_right r
                     FStar_Syntax_Syntax.unit_const_with_range
                    in
                 FStar_All.pipe_right uu____32197
                   (fun uu____32200  ->
                      FStar_Pervasives_Native.Some uu____32200)
             | uu____32201 -> FStar_Pervasives_Native.None)
         in
      let b =
        FStar_List.fold_left
          (fun b  ->
             fun imp  ->
               let uu____32214 =
                 let uu____32216 =
                   FStar_Syntax_Unionfind.find
                     (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 FStar_All.pipe_right uu____32216 FStar_Util.is_none  in
               if uu____32214
               then
                 let uu____32224 = imp_value imp  in
                 match uu____32224 with
                 | FStar_Pervasives_Native.Some tm ->
                     (commit
                        [TERM ((imp.FStar_TypeChecker_Common.imp_uvar), tm)];
                      true)
                 | FStar_Pervasives_Native.None  -> b
               else b) false imps
         in
      (imps, b)
  
let (resolve_implicits' :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun must_total  ->
      fun forcelax  ->
        fun g  ->
          let rec unresolved ctx_u =
            let uu____32267 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32267 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32274 ->
                     let uu____32275 =
                       let uu____32276 = FStar_Syntax_Subst.compress r  in
                       uu____32276.FStar_Syntax_Syntax.n  in
                     (match uu____32275 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32281) ->
                          unresolved ctx_u'
                      | uu____32298 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32322 = acc  in
            match uu____32322 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then
                       let uu____32333 =
                         try_solve_single_valued_implicits env out  in
                       (match uu____32333 with
                        | (out1,changed1) ->
                            if changed1
                            then until_fixpoint ([], false) out1
                            else out1)
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____32356 = hd  in
                     (match uu____32356 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____32367 = unresolved ctx_u  in
                             if uu____32367
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32378 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32378
                                     then
                                       let uu____32382 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32382
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32391 = teq_nosmt env1 t tm
                                          in
                                       match uu____32391 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4405_32401 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4405_32401.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4405_32401.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4405_32401.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4405_32401.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4405_32401.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4405_32401.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4405_32401.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4408_32403 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4408_32403.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4408_32403.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4408_32403.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl)))
                               | uu____32406 ->
                                   until_fixpoint ((hd :: out), changed) tl
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl
                               else
                                 (let env1 =
                                    let uu___4413_32418 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4413_32418.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4413_32418.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4413_32418.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4413_32418.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4413_32418.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4413_32418.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4413_32418.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4413_32418.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4413_32418.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4413_32418.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4413_32418.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4413_32418.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4413_32418.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4413_32418.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4413_32418.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4413_32418.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4413_32418.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4413_32418.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4413_32418.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4413_32418.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4413_32418.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4413_32418.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4413_32418.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4413_32418.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4413_32418.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4413_32418.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4413_32418.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4413_32418.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4413_32418.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4413_32418.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4413_32418.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4413_32418.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4413_32418.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4413_32418.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4413_32418.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4413_32418.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4413_32418.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4413_32418.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4413_32418.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4413_32418.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4413_32418.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4413_32418.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4413_32418.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4413_32418.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4413_32418.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___4413_32418.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4418_32423 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4418_32423.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4418_32423.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4418_32423.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4418_32423.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4418_32423.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4418_32423.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4418_32423.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4418_32423.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4418_32423.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4418_32423.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4418_32423.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4418_32423.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4418_32423.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4418_32423.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4418_32423.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4418_32423.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4418_32423.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4418_32423.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4418_32423.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4418_32423.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4418_32423.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4418_32423.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4418_32423.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4418_32423.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4418_32423.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4418_32423.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4418_32423.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4418_32423.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4418_32423.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4418_32423.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4418_32423.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4418_32423.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4418_32423.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4418_32423.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4418_32423.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4418_32423.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4418_32423.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4418_32423.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4418_32423.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4418_32423.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4418_32423.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4418_32423.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4418_32423.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4418_32423.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4418_32423.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4418_32423.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      }
                                    else env1  in
                                  (let uu____32428 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32428
                                   then
                                     let uu____32433 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32435 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32437 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32439 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32433 uu____32435 uu____32437
                                       reason uu____32439
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4424_32446  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32453 =
                                             let uu____32463 =
                                               let uu____32471 =
                                                 let uu____32473 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32475 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32477 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32473 uu____32475
                                                   uu____32477
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32471, r)
                                                in
                                             [uu____32463]  in
                                           FStar_Errors.add_errors
                                             uu____32453);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32496 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32507  ->
                                               let uu____32508 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32510 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32512 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32508 uu____32510
                                                 reason uu____32512)) env2 g1
                                         true
                                        in
                                     match uu____32496 with
                                     | FStar_Pervasives_Native.Some g2 -> g2
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Common.implicits
                                         out), true) tl)))))
             in
          let uu___4436_32520 = g  in
          let uu____32521 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4436_32520.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4436_32520.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4436_32520.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4436_32520.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32521
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____32536 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32536
       then
         let uu____32541 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32541
       else ());
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env  ->
    fun g  ->
      (let uu____32572 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32572
       then
         let uu____32577 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32577
       else ());
      (let g1 = solve_deferred_constraints env g  in
       let g2 = resolve_implicits env g1  in
       match g2.FStar_TypeChecker_Common.implicits with
       | [] ->
           let uu____32584 = discharge_guard env g2  in
           FStar_All.pipe_left (fun uu____32585  -> ()) uu____32584
       | imp::uu____32587 ->
           let uu____32590 =
             let uu____32596 =
               let uu____32598 =
                 FStar_Syntax_Print.uvar_to_string
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                  in
               let uu____32600 =
                 FStar_TypeChecker_Normalize.term_to_string env
                   (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                  in
               FStar_Util.format3
                 "Failed to resolve implicit argument %s of type %s introduced for %s"
                 uu____32598 uu____32600
                 imp.FStar_TypeChecker_Common.imp_reason
                in
             (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32596)
              in
           FStar_Errors.raise_error uu____32590
             imp.FStar_TypeChecker_Common.imp_range)
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32620 = teq env t1 t2  in
        force_trivial_guard env uu____32620
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32639 = teq_nosmt env t1 t2  in
        match uu____32639 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (layered_effect_teq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        Prims.string FStar_Pervasives_Native.option ->
          FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        fun reason  ->
          (let uu____32675 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsEqns")
              in
           if uu____32675
           then
             let uu____32680 =
               let uu____32682 =
                 FStar_All.pipe_right reason FStar_Util.is_none  in
               if uu____32682
               then "_"
               else FStar_All.pipe_right reason FStar_Util.must  in
             let uu____32699 = FStar_Syntax_Print.term_to_string t1  in
             let uu____32701 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print3 "Layered Effect (%s) %s = %s\n" uu____32680
               uu____32699 uu____32701
           else ());
          teq env t1 t2
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4474_32717 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4474_32717.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4474_32717.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4474_32717.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4474_32717.FStar_TypeChecker_Common.implicits)
      }
  
let (check_subtyping :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * FStar_TypeChecker_Common.guard_t)
          FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32753 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32753
         then
           let uu____32758 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32760 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32758
             uu____32760
         else ());
        (let uu____32765 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32765 with
         | (prob,x,wl) ->
             let g =
               let uu____32784 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32795  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32784  in
             ((let uu____32817 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____32817
               then
                 let uu____32822 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____32824 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____32826 =
                   let uu____32828 = FStar_Util.must g  in
                   guard_to_string env uu____32828  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32822 uu____32824 uu____32826
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   FStar_Pervasives_Native.Some (x, g1))))
  
let (get_subtyping_predicate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32865 = check_subtyping env t1 t2  in
        match uu____32865 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32884 =
              let uu____32885 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32885 g  in
            FStar_Pervasives_Native.Some uu____32884
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32904 = check_subtyping env t1 t2  in
        match uu____32904 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32923 =
              let uu____32924 =
                let uu____32925 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32925]  in
              FStar_TypeChecker_Env.close_guard env uu____32924 g  in
            FStar_Pervasives_Native.Some uu____32923
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32963 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32963
         then
           let uu____32968 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32970 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32968
             uu____32970
         else ());
        (let uu____32975 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32975 with
         | (prob,x,wl) ->
             let g =
               let uu____32990 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____33001  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32990  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____33026 =
                      let uu____33027 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____33027]  in
                    FStar_TypeChecker_Env.close_guard env uu____33026 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33068 = subtype_nosmt env t1 t2  in
        match uu____33068 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  