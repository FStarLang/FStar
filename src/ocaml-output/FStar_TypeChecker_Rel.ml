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
  
let (find_user_tac_for_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.ctx_uvar ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun u  ->
      match u.FStar_Syntax_Syntax.ctx_uvar_meta with
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
          a) ->
          let hooks =
            FStar_TypeChecker_Env.lookup_attr env
              FStar_Parser_Const.resolve_implicits_attr_string
             in
          FStar_All.pipe_right hooks
            (FStar_Util.try_find
               (fun hook  ->
                  FStar_All.pipe_right hook.FStar_Syntax_Syntax.sigattrs
                    (FStar_Util.for_some (FStar_Syntax_Util.attr_eq a))))
      | uu____2402 -> FStar_Pervasives_Native.None
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___303_2422 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___303_2422.wl_deferred);
         wl_deferred_to_tac = (uu___303_2422.wl_deferred_to_tac);
         ctr = (uu___303_2422.ctr);
         defer_ok = (uu___303_2422.defer_ok);
         smt_ok = (uu___303_2422.smt_ok);
         umax_heuristic_ok = (uu___303_2422.umax_heuristic_ok);
         tcenv = (uu___303_2422.tcenv);
         wl_implicits = (uu___303_2422.wl_implicits);
         repr_subcomp_allowed = (uu___303_2422.repr_subcomp_allowed)
       })
  
let mk_eq2 :
  'uuuuuu2436 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2436 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____2470 = FStar_Syntax_Util.type_u ()  in
            match uu____2470 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____2482 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____2482 with
                 | (uu____2494,tt,wl1) ->
                     let uu____2497 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2497, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2503  ->
    match uu___14_2503 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun uu____2509  -> FStar_TypeChecker_Common.TProb uu____2509)
          (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun uu____2515  -> FStar_TypeChecker_Common.CProb uu____2515)
          (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2523 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2523 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2543  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'uuuuuu2585 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'uuuuuu2585 ->
            FStar_TypeChecker_Common.rel ->
              'uuuuuu2585 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuuu2585 FStar_TypeChecker_Common.problem * worklist)
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
                        let uu____2672 =
                          let uu____2681 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2681]  in
                        FStar_List.append scope uu____2672
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2724 =
                      let uu____2727 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2727  in
                    FStar_List.append uu____2724
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2746 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2746 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2766 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2766;
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
                  (let uu____2840 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2840 with
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
                  (let uu____2928 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2928 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'uuuuuu2966 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2966 ->
          FStar_TypeChecker_Common.rel ->
            'uuuuuu2966 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('uuuuuu2966 FStar_TypeChecker_Common.problem * worklist)
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
                          let uu____3034 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3034]  in
                        let uu____3053 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____3053
                     in
                  let uu____3056 =
                    let uu____3063 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___386_3074 = wl  in
                       {
                         attempting = (uu___386_3074.attempting);
                         wl_deferred = (uu___386_3074.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___386_3074.wl_deferred_to_tac);
                         ctr = (uu___386_3074.ctr);
                         defer_ok = (uu___386_3074.defer_ok);
                         smt_ok = (uu___386_3074.smt_ok);
                         umax_heuristic_ok =
                           (uu___386_3074.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___386_3074.wl_implicits);
                         repr_subcomp_allowed =
                           (uu___386_3074.repr_subcomp_allowed)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____3063
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____3056 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____3086 =
                              let uu____3087 =
                                let uu____3096 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.as_arg uu____3096
                                 in
                              [uu____3087]  in
                            FStar_Syntax_Syntax.mk_Tm_app lg uu____3086 loc
                         in
                      let prob =
                        let uu____3124 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____3124;
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
                let uu____3172 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____3172;
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
  'uuuuuu3187 .
    worklist ->
      'uuuuuu3187 FStar_TypeChecker_Common.problem ->
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
              let uu____3220 =
                let uu____3223 =
                  let uu____3224 =
                    let uu____3231 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____3231)  in
                  FStar_Syntax_Syntax.NT uu____3224  in
                [uu____3223]  in
              FStar_Syntax_Subst.subst uu____3220 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____3253 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____3253
        then
          let uu____3261 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____3264 = prob_to_string env d  in
          let uu____3266 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____3273 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3261 uu____3264 uu____3266 uu____3273
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____3285 -> failwith "impossible"  in
           let uu____3288 =
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
           match uu____3288 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3331  ->
            match uu___15_3331 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3345 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____3349 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3349 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_3380  ->
           match uu___16_3380 with
           | UNIV uu____3383 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____3390 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____3390
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
        (fun uu___17_3418  ->
           match uu___17_3418 with
           | UNIV (u',t) ->
               let uu____3423 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____3423
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3430 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3442 =
        let uu____3443 =
          let uu____3444 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3444
           in
        FStar_Syntax_Subst.compress uu____3443  in
      FStar_All.pipe_right uu____3442 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3456 =
        let uu____3457 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3457  in
      FStar_All.pipe_right uu____3456 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3469 =
        let uu____3473 =
          let uu____3475 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3475  in
        FStar_Pervasives_Native.Some uu____3473  in
      FStar_Profiling.profile (fun uu____3478  -> sn' env t) uu____3469
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
          let uu____3503 =
            let uu____3507 =
              let uu____3509 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3509  in
            FStar_Pervasives_Native.Some uu____3507  in
          FStar_Profiling.profile
            (fun uu____3512  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3503
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3520 = FStar_Syntax_Util.head_and_args t  in
    match uu____3520 with
    | (h,uu____3539) ->
        let uu____3564 =
          let uu____3565 = FStar_Syntax_Subst.compress h  in
          uu____3565.FStar_Syntax_Syntax.n  in
        (match uu____3564 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3570 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3583 =
        let uu____3587 =
          let uu____3589 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3589  in
        FStar_Pervasives_Native.Some uu____3587  in
      FStar_Profiling.profile
        (fun uu____3594  ->
           let uu____3595 = should_strongly_reduce t  in
           if uu____3595
           then
             let uu____3598 =
               let uu____3599 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3599  in
             FStar_All.pipe_right uu____3598 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3583 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'uuuuuu3610 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu3610) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu3610)
  =
  fun env  ->
    fun t  ->
      let uu____3633 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3633, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3685  ->
              match uu____3685 with
              | (x,imp) ->
                  let uu____3704 =
                    let uu___492_3705 = x  in
                    let uu____3706 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___492_3705.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___492_3705.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3706
                    }  in
                  (uu____3704, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3730 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3730
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3734 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3734
        | uu____3737 -> u2  in
      let uu____3738 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3738
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3755 =
          let uu____3759 =
            let uu____3761 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3761  in
          FStar_Pervasives_Native.Some uu____3759  in
        FStar_Profiling.profile
          (fun uu____3764  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3755 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3886 = norm_refinement env t12  in
                 match uu____3886 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3901;
                     FStar_Syntax_Syntax.vars = uu____3902;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3926 =
                       let uu____3928 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3930 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3928 uu____3930
                        in
                     failwith uu____3926)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3946 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm uu____3946
          | FStar_Syntax_Syntax.Tm_uinst uu____3947 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3984 =
                   let uu____3985 = FStar_Syntax_Subst.compress t1'  in
                   uu____3985.FStar_Syntax_Syntax.n  in
                 match uu____3984 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4000 -> aux true t1'
                 | uu____4008 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____4023 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4054 =
                   let uu____4055 = FStar_Syntax_Subst.compress t1'  in
                   uu____4055.FStar_Syntax_Syntax.n  in
                 match uu____4054 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4070 -> aux true t1'
                 | uu____4078 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4093 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4140 =
                   let uu____4141 = FStar_Syntax_Subst.compress t1'  in
                   uu____4141.FStar_Syntax_Syntax.n  in
                 match uu____4140 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4156 -> aux true t1'
                 | uu____4164 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____4179 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____4194 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____4209 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____4224 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____4239 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____4268 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____4301 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____4322 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____4349 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____4377 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____4414 ->
              let uu____4421 =
                let uu____4423 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4425 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4423 uu____4425
                 in
              failwith uu____4421
          | FStar_Syntax_Syntax.Tm_ascribed uu____4440 ->
              let uu____4467 =
                let uu____4469 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4471 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4469 uu____4471
                 in
              failwith uu____4467
          | FStar_Syntax_Syntax.Tm_delayed uu____4486 ->
              let uu____4501 =
                let uu____4503 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4505 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4503 uu____4505
                 in
              failwith uu____4501
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4520 =
                let uu____4522 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4524 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4522 uu____4524
                 in
              failwith uu____4520
           in
        let uu____4539 = whnf env t1  in aux false uu____4539
  
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
      let uu____4584 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4584 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4625 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4625, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta  ->
    fun env  ->
      fun t  ->
        let uu____4652 = base_and_refinement_maybe_delta delta env t  in
        match uu____4652 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4712  ->
    match uu____4712 with
    | (t_base,refopt) ->
        let uu____4743 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4743 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4785 =
      let uu____4789 =
        let uu____4792 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4817  ->
                  match uu____4817 with | (uu____4825,uu____4826,x) -> x))
           in
        FStar_List.append wl.attempting uu____4792  in
      FStar_List.map (wl_prob_to_string wl) uu____4789  in
    FStar_All.pipe_right uu____4785 (FStar_String.concat "\n\t")
  
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
  fun uu____4886  ->
    match uu____4886 with
    | Flex (uu____4888,u,uu____4890) -> u.FStar_Syntax_Syntax.ctx_uvar_reason
  
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4897  ->
    match uu____4897 with
    | Flex (uu____4899,c,args) ->
        let uu____4902 = print_ctx_uvar c  in
        let uu____4904 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4902 uu____4904
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4914 = FStar_Syntax_Util.head_and_args t  in
    match uu____4914 with
    | (head,_args) ->
        let uu____4958 =
          let uu____4959 = FStar_Syntax_Subst.compress head  in
          uu____4959.FStar_Syntax_Syntax.n  in
        (match uu____4958 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4963 -> true
         | uu____4977 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4985 = FStar_Syntax_Util.head_and_args t  in
    match uu____4985 with
    | (head,_args) ->
        let uu____5028 =
          let uu____5029 = FStar_Syntax_Subst.compress head  in
          uu____5029.FStar_Syntax_Syntax.n  in
        (match uu____5028 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____5033) -> u
         | uu____5050 -> failwith "Not a flex-uvar")
  
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0  ->
    fun wl  ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x  in
        let t_x' = FStar_Syntax_Subst.subst' s t_x  in
        let uu____5086 =
          let uu____5087 = FStar_Syntax_Subst.compress t_x'  in
          uu____5087.FStar_Syntax_Syntax.n  in
        match uu____5086 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____5092 -> false  in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____5108 -> true  in
      let uu____5110 = FStar_Syntax_Util.head_and_args t0  in
      match uu____5110 with
      | (head,args) ->
          let uu____5157 =
            let uu____5158 = FStar_Syntax_Subst.compress head  in
            uu____5158.FStar_Syntax_Syntax.n  in
          (match uu____5157 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____5166)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5182) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____5223 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               (match uu____5223 with
                | (gamma_aff,new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____5250 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff
                            in
                         let uu____5254 =
                           let uu____5261 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma
                              in
                           let uu____5270 =
                             let uu____5273 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             FStar_Syntax_Util.arrow dom_binders uu____5273
                              in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____5261
                             uu____5270
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta
                            in
                         (match uu____5254 with
                          | (v,t_v,wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____5309  ->
                                     match uu____5309 with
                                     | (x,i) ->
                                         let uu____5328 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____5328, i)) dom_binders
                                 in
                              let sol =
                                FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                  t0.FStar_Syntax_Syntax.pos
                                 in
                              (FStar_Syntax_Util.set_uvar
                                 uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                               (let args_sol_s =
                                  FStar_List.map
                                    (fun uu____5358  ->
                                       match uu____5358 with
                                       | (a,i) ->
                                           let uu____5377 =
                                             FStar_Syntax_Subst.subst' s a
                                              in
                                           (uu____5377, i)) args_sol
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    t0.FStar_Syntax_Syntax.pos
                                   in
                                (t, wl1))))))
           | uu____5387 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
  
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t  ->
    let uu____5399 = FStar_Syntax_Util.head_and_args t  in
    match uu____5399 with
    | (head,args) ->
        let uu____5442 =
          let uu____5443 = FStar_Syntax_Subst.compress head  in
          uu____5443.FStar_Syntax_Syntax.n  in
        (match uu____5442 with
         | FStar_Syntax_Syntax.Tm_uvar (uv,s) -> Flex (t, uv, args)
         | uu____5464 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t  ->
    fun wl  ->
      let uu____5485 = ensure_no_uvar_subst t wl  in
      match uu____5485 with
      | (t1,wl1) ->
          let uu____5496 = destruct_flex_t' t1  in (uu____5496, wl1)
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5513 =
          let uu____5536 =
            let uu____5537 = FStar_Syntax_Subst.compress k  in
            uu____5537.FStar_Syntax_Syntax.n  in
          match uu____5536 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5619 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5619)
              else
                (let uu____5654 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5654 with
                 | (ys',t1,uu____5687) ->
                     let uu____5692 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5692))
          | uu____5731 ->
              let uu____5732 =
                let uu____5737 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5737)  in
              ((ys, t), uu____5732)
           in
        match uu____5513 with
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
                 let uu____5832 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5832 c  in
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
               (let uu____5910 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5910
                then
                  let uu____5915 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5917 = print_ctx_uvar uv  in
                  let uu____5919 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5915 uu____5917 uu____5919
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5928 =
                   let uu____5930 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5930  in
                 let uu____5933 =
                   let uu____5936 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5936
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5928 uu____5933 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail uu____5969 =
               let uu____5970 =
                 let uu____5972 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5974 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5972 uu____5974
                  in
               failwith uu____5970  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____6040  ->
                       match uu____6040 with
                       | (a,i) ->
                           let uu____6061 =
                             let uu____6062 = FStar_Syntax_Subst.compress a
                                in
                             uu____6062.FStar_Syntax_Syntax.n  in
                           (match uu____6061 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____6088 -> (fail (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____6098 =
                 let uu____6100 = is_flex g  in Prims.op_Negation uu____6100
                  in
               if uu____6098
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____6109 = destruct_flex_t g wl  in
                  match uu____6109 with
                  | (Flex (uu____6114,uv1,args),wl1) ->
                      ((let uu____6119 = args_as_binders args  in
                        assign_solution uu____6119 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___770_6121 = wl1  in
              {
                attempting = (uu___770_6121.attempting);
                wl_deferred = (uu___770_6121.wl_deferred);
                wl_deferred_to_tac = (uu___770_6121.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___770_6121.defer_ok);
                smt_ok = (uu___770_6121.smt_ok);
                umax_heuristic_ok = (uu___770_6121.umax_heuristic_ok);
                tcenv = (uu___770_6121.tcenv);
                wl_implicits = (uu___770_6121.wl_implicits);
                repr_subcomp_allowed = (uu___770_6121.repr_subcomp_allowed)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____6146 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____6146
         then
           let uu____6151 = FStar_Util.string_of_int pid  in
           let uu____6153 = uvis_to_string wl.tcenv sol  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6151 uu____6153
         else ());
        commit sol;
        (let uu___778_6159 = wl  in
         {
           attempting = (uu___778_6159.attempting);
           wl_deferred = (uu___778_6159.wl_deferred);
           wl_deferred_to_tac = (uu___778_6159.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___778_6159.defer_ok);
           smt_ok = (uu___778_6159.smt_ok);
           umax_heuristic_ok = (uu___778_6159.umax_heuristic_ok);
           tcenv = (uu___778_6159.tcenv);
           wl_implicits = (uu___778_6159.wl_implicits);
           repr_subcomp_allowed = (uu___778_6159.repr_subcomp_allowed)
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
          (let uu____6195 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____6195
           then
             let uu____6200 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____6204 = uvis_to_string wl.tcenv uvis  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6200 uu____6204
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
        let uu____6231 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____6231 FStar_Util.set_elements  in
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
      let uu____6271 = occurs uk t  in
      match uu____6271 with
      | (uvars,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6310 =
                 let uu____6312 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____6314 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6312 uu____6314
                  in
               FStar_Pervasives_Native.Some uu____6310)
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
          let uu____6425 = FStar_Syntax_Syntax.bv_eq b b'  in
          if uu____6425
          then
            let uu____6436 = maximal_prefix bs_tail bs'_tail  in
            (match uu____6436 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6487 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6544  ->
             match uu____6544 with
             | (x,uu____6556) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6574 = FStar_List.last bs  in
      match uu____6574 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6598) ->
          let uu____6609 =
            FStar_Util.prefix_until
              (fun uu___18_6624  ->
                 match uu___18_6624 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6627 -> false) g
             in
          (match uu____6609 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6641,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6678 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6678 with
        | (pfx,uu____6688) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6700 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6700 with
             | (uu____6708,src',wl1) ->
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
                 | uu____6822 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6823 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6887  ->
                  fun uu____6888  ->
                    match (uu____6887, uu____6888) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6991 =
                          let uu____6993 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6993
                           in
                        if uu____6991
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____7027 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____7027
                           then
                             let uu____7044 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____7044)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6823 with | (isect,uu____7094) -> FStar_List.rev isect
  
let binders_eq :
  'uuuuuu7130 'uuuuuu7131 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu7130) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7131) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7189  ->
              fun uu____7190  ->
                match (uu____7189, uu____7190) with
                | ((a,uu____7209),(b,uu____7211)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'uuuuuu7227 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7227) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____7258  ->
           match uu____7258 with
           | (y,uu____7265) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'uuuuuu7275 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7275) Prims.list ->
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
                   let uu____7437 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____7437
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7470 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7522 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7566 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7587 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7595  ->
    match uu___19_7595 with
    | MisMatch (d1,d2) ->
        let uu____7607 =
          let uu____7609 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7611 =
            let uu____7613 =
              let uu____7615 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7615 ")"  in
            Prims.op_Hat ") (" uu____7613  in
          Prims.op_Hat uu____7609 uu____7611  in
        Prims.op_Hat "MisMatch (" uu____7607
    | HeadMatch u ->
        let uu____7622 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7622
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___20_7631  ->
    match uu___20_7631 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7648 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7663 =
            (let uu____7669 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                in
             let uu____7671 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             uu____7669 = uu____7671) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
             in
          if uu____7663 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7680 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7680 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7691 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7715 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7725 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7744 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7744
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7745 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7746 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7747 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7760 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7774 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7798) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7804,uu____7805) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7847) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7872;
             FStar_Syntax_Syntax.index = uu____7873;
             FStar_Syntax_Syntax.sort = t2;_},uu____7875)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7883 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7884 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7885 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7900 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7907 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7927 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7927
  
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
           { FStar_Syntax_Syntax.blob = uu____7946;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7947;
             FStar_Syntax_Syntax.ltyp = uu____7948;
             FStar_Syntax_Syntax.rng = uu____7949;_},uu____7950)
            ->
            let uu____7961 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7961 t21
        | (uu____7962,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7963;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7964;
             FStar_Syntax_Syntax.ltyp = uu____7965;
             FStar_Syntax_Syntax.rng = uu____7966;_})
            ->
            let uu____7977 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7977
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7980 = FStar_Syntax_Syntax.bv_eq x y  in
            if uu____7980
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7991 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7991
            then FullMatch
            else
              (let uu____7996 =
                 let uu____8005 =
                   let uu____8008 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____8008  in
                 let uu____8009 =
                   let uu____8012 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____8012  in
                 (uu____8005, uu____8009)  in
               MisMatch uu____7996)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____8018),FStar_Syntax_Syntax.Tm_uinst (g,uu____8020)) ->
            let uu____8029 = head_matches env f g  in
            FStar_All.pipe_right uu____8029 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____8030) -> HeadMatch true
        | (uu____8032,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____8036 = FStar_Const.eq_const c d  in
            if uu____8036
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____8046),FStar_Syntax_Syntax.Tm_uvar (uv',uu____8048)) ->
            let uu____8081 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____8081
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____8091),FStar_Syntax_Syntax.Tm_refine (y,uu____8093)) ->
            let uu____8102 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8102 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____8104),uu____8105) ->
            let uu____8110 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____8110 head_match
        | (uu____8111,FStar_Syntax_Syntax.Tm_refine (x,uu____8113)) ->
            let uu____8118 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8118 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8119,FStar_Syntax_Syntax.Tm_type
           uu____8120) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____8122,FStar_Syntax_Syntax.Tm_arrow uu____8123) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____8154),FStar_Syntax_Syntax.Tm_app (head',uu____8156))
            ->
            let uu____8205 = head_matches env head head'  in
            FStar_All.pipe_right uu____8205 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____8207),uu____8208) ->
            let uu____8233 = head_matches env head t21  in
            FStar_All.pipe_right uu____8233 head_match
        | (uu____8234,FStar_Syntax_Syntax.Tm_app (head,uu____8236)) ->
            let uu____8261 = head_matches env t11 head  in
            FStar_All.pipe_right uu____8261 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8262,FStar_Syntax_Syntax.Tm_let
           uu____8263) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____8291,FStar_Syntax_Syntax.Tm_match uu____8292) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8338,FStar_Syntax_Syntax.Tm_abs
           uu____8339) -> HeadMatch true
        | uu____8377 ->
            let uu____8382 =
              let uu____8391 = delta_depth_of_term env t11  in
              let uu____8394 = delta_depth_of_term env t21  in
              (uu____8391, uu____8394)  in
            MisMatch uu____8382
  
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
              let uu____8463 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8463  in
            (let uu____8465 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8465
             then
               let uu____8470 = FStar_Syntax_Print.term_to_string t  in
               let uu____8472 = FStar_Syntax_Print.term_to_string head  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8470 uu____8472
             else ());
            (let uu____8477 =
               let uu____8478 = FStar_Syntax_Util.un_uinst head  in
               uu____8478.FStar_Syntax_Syntax.n  in
             match uu____8477 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8484 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8484 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8498 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8498
                        then
                          let uu____8503 =
                            FStar_Syntax_Print.term_to_string head  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8503
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8508 ->
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
                      let uu____8526 =
                        let uu____8528 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8528 = FStar_Syntax_Util.Equal  in
                      if uu____8526
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8535 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8535
                          then
                            let uu____8540 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8542 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8540
                              uu____8542
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8547 -> FStar_Pervasives_Native.None)
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
            (let uu____8699 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8699
             then
               let uu____8704 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8706 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8708 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8704
                 uu____8706 uu____8708
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8736 =
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
               match uu____8736 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8784 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8784 with
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
                  uu____8822),uu____8823)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8844 =
                      let uu____8853 = maybe_inline t11  in
                      let uu____8856 = maybe_inline t21  in
                      (uu____8853, uu____8856)  in
                    match uu____8844 with
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
                 (uu____8899,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8900))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8921 =
                      let uu____8930 = maybe_inline t11  in
                      let uu____8933 = maybe_inline t21  in
                      (uu____8930, uu____8933)  in
                    match uu____8921 with
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
             | MisMatch uu____8988 -> fail n_delta r t11 t21
             | uu____8997 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____9012 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____9012
           then
             let uu____9017 = FStar_Syntax_Print.term_to_string t1  in
             let uu____9019 = FStar_Syntax_Print.term_to_string t2  in
             let uu____9021 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____9029 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____9046 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____9046
                    (fun uu____9081  ->
                       match uu____9081 with
                       | (t11,t21) ->
                           let uu____9089 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____9091 =
                             let uu____9093 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____9093  in
                           Prims.op_Hat uu____9089 uu____9091))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____9017 uu____9019 uu____9021 uu____9029
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____9110 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____9110 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_9125  ->
    match uu___21_9125 with
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
      let uu___1267_9174 = p  in
      let uu____9177 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____9178 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1267_9174.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9177;
        FStar_TypeChecker_Common.relation =
          (uu___1267_9174.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9178;
        FStar_TypeChecker_Common.element =
          (uu___1267_9174.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1267_9174.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1267_9174.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1267_9174.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1267_9174.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1267_9174.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9193 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____9193
            (fun uu____9198  -> FStar_TypeChecker_Common.TProb uu____9198)
      | FStar_TypeChecker_Common.CProb uu____9199 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____9222 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____9222 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9230 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9230 with
           | (lh,lhs_args) ->
               let uu____9277 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9277 with
                | (rh,rhs_args) ->
                    let uu____9324 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9337,FStar_Syntax_Syntax.Tm_uvar uu____9338)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9427 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9454,uu____9455)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9470,FStar_Syntax_Syntax.Tm_uvar uu____9471)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9486,FStar_Syntax_Syntax.Tm_arrow uu____9487)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1318_9517 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1318_9517.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1318_9517.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1318_9517.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1318_9517.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1318_9517.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1318_9517.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1318_9517.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1318_9517.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1318_9517.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9520,FStar_Syntax_Syntax.Tm_type uu____9521)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1318_9537 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1318_9537.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1318_9537.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1318_9537.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1318_9537.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1318_9537.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1318_9537.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1318_9537.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1318_9537.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1318_9537.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9540,FStar_Syntax_Syntax.Tm_uvar uu____9541)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1318_9557 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1318_9557.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1318_9557.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1318_9557.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1318_9557.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1318_9557.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1318_9557.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1318_9557.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1318_9557.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1318_9557.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9560,FStar_Syntax_Syntax.Tm_uvar uu____9561)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9576,uu____9577)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9592,FStar_Syntax_Syntax.Tm_uvar uu____9593)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9608,uu____9609) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9324 with
                     | (rank,tp1) ->
                         let uu____9622 =
                           FStar_All.pipe_right
                             (let uu___1338_9626 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1338_9626.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1338_9626.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1338_9626.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1338_9626.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1338_9626.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1338_9626.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1338_9626.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1338_9626.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1338_9626.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9629  ->
                                FStar_TypeChecker_Common.TProb uu____9629)
                            in
                         (rank, uu____9622))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9633 =
            FStar_All.pipe_right
              (let uu___1342_9637 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1342_9637.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1342_9637.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1342_9637.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1342_9637.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1342_9637.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1342_9637.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1342_9637.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1342_9637.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1342_9637.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9640  -> FStar_TypeChecker_Common.CProb uu____9640)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9633)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9700 probs =
      match uu____9700 with
      | (min_rank,min,out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9781 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9802 = rank wl.tcenv hd  in
               (match uu____9802 with
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
                      (let uu____9863 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9868 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9868)
                          in
                       if uu____9863
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
          let uu____9941 = FStar_Syntax_Util.head_and_args t  in
          match uu____9941 with
          | (hd,uu____9960) ->
              let uu____9985 =
                let uu____9986 = FStar_Syntax_Subst.compress hd  in
                uu____9986.FStar_Syntax_Syntax.n  in
              (match uu____9985 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9991) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____10026  ->
                           match uu____10026 with
                           | (y,uu____10035) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____10058  ->
                                       match uu____10058 with
                                       | (x,uu____10067) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____10072 -> false)
           in
        let uu____10074 = rank tcenv p  in
        match uu____10074 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____10083 -> true
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
    match projectee with | UDeferred _0 -> true | uu____10164 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____10183 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____10202 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____10219 = FStar_Thunk.mkv s  in UFailed uu____10219 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____10234 = mklstr s  in UFailed uu____10234 
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
                        let uu____10285 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____10285 with
                        | (k,uu____10293) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10308 -> false)))
            | uu____10310 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10362 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  FStar_Syntax_Util.eq_univs uv1 uv2))
                           in
                        if uu____10362 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____10386 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  -> FStar_Syntax_Util.eq_univs u u'))
                      in
                   Prims.op_Negation uu____10386)
               in
            let uu____10393 = filter u12  in
            let uu____10396 = filter u22  in (uu____10393, uu____10396)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10431 = filter_out_common_univs us1 us2  in
                   (match uu____10431 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10491 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10491 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10494 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10511  ->
                               let uu____10512 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10514 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10512 uu____10514))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10540 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10540 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10566 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10566 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10569 ->
                   ufailed_thunk
                     (fun uu____10580  ->
                        let uu____10581 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10583 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10581 uu____10583 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10586,uu____10587) ->
              let uu____10589 =
                let uu____10591 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10593 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10591 uu____10593
                 in
              failwith uu____10589
          | (FStar_Syntax_Syntax.U_unknown ,uu____10596) ->
              let uu____10597 =
                let uu____10599 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10601 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10599 uu____10601
                 in
              failwith uu____10597
          | (uu____10604,FStar_Syntax_Syntax.U_bvar uu____10605) ->
              let uu____10607 =
                let uu____10609 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10611 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10609 uu____10611
                 in
              failwith uu____10607
          | (uu____10614,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10615 =
                let uu____10617 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10619 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10617 uu____10619
                 in
              failwith uu____10615
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              let uu____10624 =
                let uu____10626 = FStar_Ident.string_of_id x  in
                let uu____10628 = FStar_Ident.string_of_id y  in
                uu____10626 = uu____10628  in
              if uu____10624
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10659 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10659
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10678 = occurs_univ v1 u3  in
              if uu____10678
              then
                let uu____10681 =
                  let uu____10683 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10685 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10683 uu____10685
                   in
                try_umax_components u11 u21 uu____10681
              else
                (let uu____10690 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10690)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10704 = occurs_univ v1 u3  in
              if uu____10704
              then
                let uu____10707 =
                  let uu____10709 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10711 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10709 uu____10711
                   in
                try_umax_components u11 u21 uu____10707
              else
                (let uu____10716 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10716)
          | (FStar_Syntax_Syntax.U_max uu____10717,uu____10718) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10726 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10726
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10732,FStar_Syntax_Syntax.U_max uu____10733) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10741 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10741
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10747,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10749,FStar_Syntax_Syntax.U_name uu____10750) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10752) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10754) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10756,FStar_Syntax_Syntax.U_succ uu____10757) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10759,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10866 = bc1  in
      match uu____10866 with
      | (bs1,mk_cod1) ->
          let uu____10910 = bc2  in
          (match uu____10910 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____11021 = aux xs ys  in
                     (match uu____11021 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____11104 =
                       let uu____11111 = mk_cod1 xs  in ([], uu____11111)  in
                     let uu____11114 =
                       let uu____11121 = mk_cod2 ys  in ([], uu____11121)  in
                     (uu____11104, uu____11114)
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
                  let uu____11190 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____11190 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____11193 =
                    let uu____11194 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____11194 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____11193
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____11199 = has_type_guard t1 t2  in (uu____11199, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____11200 = has_type_guard t2 t1  in (uu____11200, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_11207  ->
    match uu___22_11207 with
    | Flex (uu____11209,uu____11210,[]) -> true
    | uu____11220 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____11234 = f  in
      match uu____11234 with
      | Flex (uu____11236,u,uu____11238) ->
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
      let uu____11262 = f  in
      match uu____11262 with
      | Flex
          (uu____11269,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____11270;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11271;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____11274;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____11275;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____11276;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____11277;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11343  ->
                 match uu____11343 with
                 | (y,uu____11352) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11506 =
                  let uu____11521 =
                    let uu____11524 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11524  in
                  ((FStar_List.rev pat_binders), uu____11521)  in
                FStar_Pervasives_Native.Some uu____11506
            | (uu____11557,[]) ->
                let uu____11588 =
                  let uu____11603 =
                    let uu____11606 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11606  in
                  ((FStar_List.rev pat_binders), uu____11603)  in
                FStar_Pervasives_Native.Some uu____11588
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11697 =
                  let uu____11698 = FStar_Syntax_Subst.compress a  in
                  uu____11698.FStar_Syntax_Syntax.n  in
                (match uu____11697 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11718 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11718
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1679_11748 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1679_11748.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1679_11748.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11752 =
                            let uu____11753 =
                              let uu____11760 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11760)  in
                            FStar_Syntax_Syntax.NT uu____11753  in
                          [uu____11752]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1685_11776 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1685_11776.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1685_11776.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11777 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11817 =
                  let uu____11824 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11824  in
                (match uu____11817 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11883 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11908 ->
               let uu____11909 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11909 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____12241 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____12241
       then
         let uu____12246 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12246
       else ());
      (let uu____12252 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____12252
       then
         let uu____12257 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12257
       else ());
      (let uu____12262 = next_prob probs  in
       match uu____12262 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1712_12289 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1712_12289.wl_deferred);
               wl_deferred_to_tac = (uu___1712_12289.wl_deferred_to_tac);
               ctr = (uu___1712_12289.ctr);
               defer_ok = (uu___1712_12289.defer_ok);
               smt_ok = (uu___1712_12289.smt_ok);
               umax_heuristic_ok = (uu___1712_12289.umax_heuristic_ok);
               tcenv = (uu___1712_12289.tcenv);
               wl_implicits = (uu___1712_12289.wl_implicits);
               repr_subcomp_allowed = (uu___1712_12289.repr_subcomp_allowed)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12298 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____12298
                 then
                   let uu____12301 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____12301
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
                           (let uu___1724_12313 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1724_12313.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1724_12313.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1724_12313.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1724_12313.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1724_12313.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1724_12313.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1724_12313.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1724_12313.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1724_12313.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12333 =
                  let uu____12340 = as_deferred probs.wl_deferred_to_tac  in
                  ([], uu____12340, (probs.wl_implicits))  in
                Success uu____12333
            | uu____12346 ->
                let uu____12356 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12421  ->
                          match uu____12421 with
                          | (c,uu____12431,uu____12432) -> c < probs.ctr))
                   in
                (match uu____12356 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12480 =
                            let uu____12487 = as_deferred probs.wl_deferred
                               in
                            let uu____12488 =
                              as_deferred probs.wl_deferred_to_tac  in
                            (uu____12487, uu____12488, (probs.wl_implicits))
                             in
                          Success uu____12480
                      | uu____12489 ->
                          let uu____12499 =
                            let uu___1738_12500 = probs  in
                            let uu____12501 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12522  ->
                                      match uu____12522 with
                                      | (uu____12530,uu____12531,y) -> y))
                               in
                            {
                              attempting = uu____12501;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1738_12500.wl_deferred_to_tac);
                              ctr = (uu___1738_12500.ctr);
                              defer_ok = (uu___1738_12500.defer_ok);
                              smt_ok = (uu___1738_12500.smt_ok);
                              umax_heuristic_ok =
                                (uu___1738_12500.umax_heuristic_ok);
                              tcenv = (uu___1738_12500.tcenv);
                              wl_implicits = (uu___1738_12500.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1738_12500.repr_subcomp_allowed)
                            }  in
                          solve env uu____12499))))

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
            let uu____12540 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12540 with
            | USolved wl1 ->
                let uu____12542 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12542
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12545 = defer_lit "" orig wl1  in
                solve env uu____12545

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
                  let uu____12596 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12596 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12599 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12612;
                  FStar_Syntax_Syntax.vars = uu____12613;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12616;
                  FStar_Syntax_Syntax.vars = uu____12617;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12630,uu____12631) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12639,FStar_Syntax_Syntax.Tm_uinst uu____12640) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12648 -> USolved wl

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
            ((let uu____12659 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12659
              then
                let uu____12664 = prob_to_string env orig  in
                let uu____12666 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12664 uu____12666
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
            let uu___1820_12681 = wl1  in
            let uu____12682 =
              let uu____12692 =
                let uu____12700 = FStar_Thunk.mkv reason  in
                ((wl1.ctr), uu____12700, orig)  in
              uu____12692 :: (wl1.wl_deferred_to_tac)  in
            {
              attempting = (uu___1820_12681.attempting);
              wl_deferred = (uu___1820_12681.wl_deferred);
              wl_deferred_to_tac = uu____12682;
              ctr = (uu___1820_12681.ctr);
              defer_ok = (uu___1820_12681.defer_ok);
              smt_ok = (uu___1820_12681.smt_ok);
              umax_heuristic_ok = (uu___1820_12681.umax_heuristic_ok);
              tcenv = (uu___1820_12681.tcenv);
              wl_implicits = (uu___1820_12681.wl_implicits);
              repr_subcomp_allowed = (uu___1820_12681.repr_subcomp_allowed)
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
                let uu____12729 = FStar_Syntax_Util.head_and_args t  in
                match uu____12729 with
                | (head,uu____12753) ->
                    let uu____12778 =
                      let uu____12779 = FStar_Syntax_Subst.compress head  in
                      uu____12779.FStar_Syntax_Syntax.n  in
                    (match uu____12778 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12789) ->
                         let uu____12806 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv
                            in
                         (uu____12806,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12810 -> (false, ""))
                 in
              let uu____12815 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs  in
              (match uu____12815 with
               | (l1,r1) ->
                   let uu____12828 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs  in
                   (match uu____12828 with
                    | (l2,r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12845 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl
                              in
                           solve env uu____12845)))
          | uu____12846 ->
              let uu____12847 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl  in
              solve env uu____12847

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
               let uu____12933 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12933 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12988 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12988
                then
                  let uu____12993 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12995 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12993 uu____12995
                else ());
               (let uu____13000 = head_matches_delta env1 wl2 t1 t2  in
                match uu____13000 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____13046 = eq_prob t1 t2 wl2  in
                         (match uu____13046 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____13067 ->
                         let uu____13076 = eq_prob t1 t2 wl2  in
                         (match uu____13076 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13126 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13141 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13142 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13141, uu____13142)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13147 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13148 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13147, uu____13148)
                            in
                         (match uu____13126 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13179 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13179 with
                                | (t1_hd,t1_args) ->
                                    let uu____13224 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13224 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13290 =
                                              let uu____13297 =
                                                let uu____13308 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____13308 :: t1_args  in
                                              let uu____13325 =
                                                let uu____13334 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____13334 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____13383  ->
                                                   fun uu____13384  ->
                                                     fun uu____13385  ->
                                                       match (uu____13383,
                                                               uu____13384,
                                                               uu____13385)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____13435),
                                                          (a2,uu____13437))
                                                           ->
                                                           let uu____13474 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13474
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13297
                                                uu____13325
                                               in
                                            match uu____13290 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1923_13500 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1923_13500.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1923_13500.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1923_13500.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1923_13500.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1923_13500.repr_subcomp_allowed)
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13511 =
                                                  solve env1 wl'  in
                                                (match uu____13511 with
                                                 | Success
                                                     (uu____13514,defer_to_tac,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13518 =
                                                         extend_wl wl4
                                                           defer_to_tac imps
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13518))
                                                 | Failed uu____13519 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13551 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13551 with
                                | (t1_base,p1_opt) ->
                                    let uu____13587 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13587 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13686 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13686
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
                                               let uu____13739 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13739
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
                                               let uu____13771 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13771
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
                                               let uu____13803 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13803
                                           | uu____13806 -> t_base  in
                                         let uu____13823 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13823 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13837 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13837, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13844 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13844 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13880 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13880 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13916 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13916
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
                              let uu____13940 = combine t11 t21 wl2  in
                              (match uu____13940 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13973 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13973
                                     then
                                       let uu____13978 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13978
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____14020 ts1 =
               match uu____14020 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____14083 = pairwise out t wl2  in
                        (match uu____14083 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14119 =
               let uu____14130 = FStar_List.hd ts  in (uu____14130, [], wl1)
                in
             let uu____14139 = FStar_List.tl ts  in
             aux uu____14119 uu____14139  in
           let uu____14146 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14146 with
           | (this_flex,this_rigid) ->
               let uu____14172 =
                 let uu____14173 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14173.FStar_Syntax_Syntax.n  in
               (match uu____14172 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14198 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14198
                    then
                      let uu____14201 = destruct_flex_t this_flex wl  in
                      (match uu____14201 with
                       | (flex,wl1) ->
                           let uu____14208 = quasi_pattern env flex  in
                           (match uu____14208 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____14227 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14227
                                  then
                                    let uu____14232 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14232
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14239 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2033_14242 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2033_14242.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2033_14242.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2033_14242.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2033_14242.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2033_14242.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2033_14242.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2033_14242.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2033_14242.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2033_14242.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14239)
                | uu____14243 ->
                    ((let uu____14245 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14245
                      then
                        let uu____14250 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14250
                      else ());
                     (let uu____14255 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14255 with
                      | (u,_args) ->
                          let uu____14298 =
                            let uu____14299 = FStar_Syntax_Subst.compress u
                               in
                            uu____14299.FStar_Syntax_Syntax.n  in
                          (match uu____14298 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____14327 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____14327 with
                                 | (u',uu____14346) ->
                                     let uu____14371 =
                                       let uu____14372 = whnf env u'  in
                                       uu____14372.FStar_Syntax_Syntax.n  in
                                     (match uu____14371 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14394 -> false)
                                  in
                               let uu____14396 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_14419  ->
                                         match uu___23_14419 with
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
                                              | uu____14433 -> false)
                                         | uu____14437 -> false))
                                  in
                               (match uu____14396 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14452 = whnf env this_rigid
                                         in
                                      let uu____14453 =
                                        FStar_List.collect
                                          (fun uu___24_14459  ->
                                             match uu___24_14459 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14465 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14465]
                                             | uu____14469 -> [])
                                          bounds_probs
                                         in
                                      uu____14452 :: uu____14453  in
                                    let uu____14470 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14470 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14503 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14518 =
                                               let uu____14519 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14519.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14518 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14531 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14531)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14542 -> bound  in
                                           let uu____14543 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14543)  in
                                         (match uu____14503 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14578 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14578
                                                then
                                                  let wl'1 =
                                                    let uu___2093_14584 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2093_14584.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2093_14584.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2093_14584.ctr);
                                                      defer_ok =
                                                        (uu___2093_14584.defer_ok);
                                                      smt_ok =
                                                        (uu___2093_14584.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2093_14584.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2093_14584.tcenv);
                                                      wl_implicits =
                                                        (uu___2093_14584.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2093_14584.repr_subcomp_allowed)
                                                    }  in
                                                  let uu____14585 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14585
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14591 =
                                                  solve_t env eq_prob
                                                    (let uu___2098_14593 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2098_14593.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2098_14593.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2098_14593.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2098_14593.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2098_14593.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2098_14593.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2098_14593.repr_subcomp_allowed)
                                                     })
                                                   in
                                                match uu____14591 with
                                                | Success
                                                    (uu____14595,defer_to_tac,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2105_14599 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2105_14599.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2105_14599.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2105_14599.ctr);
                                                        defer_ok =
                                                          (uu___2105_14599.defer_ok);
                                                        smt_ok =
                                                          (uu___2105_14599.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2105_14599.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2105_14599.tcenv);
                                                        wl_implicits =
                                                          (uu___2105_14599.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2105_14599.repr_subcomp_allowed)
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
                                                    let uu____14616 =
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
                                                    ((let uu____14628 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14628
                                                      then
                                                        let uu____14633 =
                                                          let uu____14635 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14635
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14633
                                                      else ());
                                                     (let uu____14648 =
                                                        let uu____14663 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14663)
                                                         in
                                                      match uu____14648 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14685))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14711 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14711
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
                                                                  let uu____14731
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14731))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14756 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14756
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
                                                                    let uu____14776
                                                                    =
                                                                    let uu____14781
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14781
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14776
                                                                    [] wl2
                                                                     in
                                                                  let uu____14787
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14787))))
                                                      | uu____14788 ->
                                                          let uu____14803 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14803 p)))))))
                           | uu____14810 when flip ->
                               let uu____14811 =
                                 let uu____14813 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14815 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14813 uu____14815
                                  in
                               failwith uu____14811
                           | uu____14818 ->
                               let uu____14819 =
                                 let uu____14821 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14823 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14821 uu____14823
                                  in
                               failwith uu____14819)))))

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
                      (fun uu____14859  ->
                         match uu____14859 with
                         | (x,i) ->
                             let uu____14878 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14878, i)) bs_lhs
                     in
                  let uu____14881 = lhs  in
                  match uu____14881 with
                  | Flex (uu____14882,u_lhs,uu____14884) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14981 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14991 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14991, univ)
                             in
                          match uu____14981 with
                          | (k,univ) ->
                              let uu____14998 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14998 with
                               | (uu____15015,u,wl3) ->
                                   let uu____15018 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____15018, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____15044 =
                              let uu____15057 =
                                let uu____15068 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____15068 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15119  ->
                                   fun uu____15120  ->
                                     match (uu____15119, uu____15120) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15221 =
                                           let uu____15228 =
                                             let uu____15231 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15231
                                              in
                                           copy_uvar u_lhs [] uu____15228 wl2
                                            in
                                         (match uu____15221 with
                                          | (uu____15260,t_a,wl3) ->
                                              let uu____15263 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____15263 with
                                               | (uu____15282,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____15057
                                ([], wl1)
                               in
                            (match uu____15044 with
                             | (out_args,wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_15351  ->
                                        match uu___25_15351 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____15353 -> false
                                        | uu____15357 -> true) flags
                                    in
                                 let ct' =
                                   let uu___2224_15360 = ct  in
                                   let uu____15361 =
                                     let uu____15364 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____15364
                                      in
                                   let uu____15379 = FStar_List.tl out_args
                                      in
                                   let uu____15396 =
                                     nodec ct.FStar_Syntax_Syntax.flags  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2224_15360.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2224_15360.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15361;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15379;
                                     FStar_Syntax_Syntax.flags = uu____15396
                                   }  in
                                 ((let uu___2227_15400 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2227_15400.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2227_15400.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____15403 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____15403 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15441 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____15441 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15452 =
                                          let uu____15457 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15457)  in
                                        TERM uu____15452  in
                                      let uu____15458 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15458 with
                                       | (sub_prob,wl3) ->
                                           let uu____15472 =
                                             let uu____15473 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15473
                                              in
                                           solve env uu____15472))
                             | (x,imp)::formals2 ->
                                 let uu____15495 =
                                   let uu____15502 =
                                     let uu____15505 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15505
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15502 wl1
                                    in
                                 (match uu____15495 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15526 =
                                          let uu____15529 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15529
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15526 u_x
                                         in
                                      let uu____15530 =
                                        let uu____15533 =
                                          let uu____15536 =
                                            let uu____15537 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15537, imp)  in
                                          [uu____15536]  in
                                        FStar_List.append bs_terms
                                          uu____15533
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15530 formals2 wl2)
                              in
                           let uu____15564 = occurs_check u_lhs arrow  in
                           (match uu____15564 with
                            | (uu____15577,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15593 =
                                    mklstr
                                      (fun uu____15598  ->
                                         let uu____15599 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15599)
                                     in
                                  giveup_or_defer env orig wl uu____15593
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
              (let uu____15632 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15632
               then
                 let uu____15637 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15640 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15637 (rel_to_string (p_rel orig)) uu____15640
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15771 = rhs wl1 scope env1 subst  in
                     (match uu____15771 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15794 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15794
                            then
                              let uu____15799 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15799
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15877 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15877 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2297_15879 = hd1  in
                       let uu____15880 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2297_15879.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2297_15879.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15880
                       }  in
                     let hd21 =
                       let uu___2300_15884 = hd2  in
                       let uu____15885 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2300_15884.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2300_15884.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15885
                       }  in
                     let uu____15888 =
                       let uu____15893 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15893
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15888 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15916 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15916
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15923 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15923 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15995 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15995
                                  in
                               ((let uu____16013 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16013
                                 then
                                   let uu____16018 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____16020 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____16018
                                     uu____16020
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____16055 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____16091 = aux wl [] env [] bs1 bs2  in
               match uu____16091 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16150 = attempt sub_probs wl2  in
                   solve env1 uu____16150)

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
            let uu___2338_16170 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2338_16170.wl_deferred_to_tac);
              ctr = (uu___2338_16170.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2338_16170.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2338_16170.repr_subcomp_allowed)
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16182 = try_solve env wl'  in
          match uu____16182 with
          | Success (uu____16183,defer_to_tac,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps  in solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16196 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16196 wl)

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
            let uu____16202 = should_defer_flex_to_user_tac wl lhs  in
            if uu____16202
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16215 =
                   FStar_List.map FStar_Pervasives_Native.fst bs  in
                 FStar_Util.as_set uu____16215 FStar_Syntax_Syntax.order_bv
                  in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16249 = lhs1  in
                 match uu____16249 with
                 | Flex (uu____16252,ctx_u,uu____16254) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16262 ->
                           let uu____16263 = sn_binders env1 bs  in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16263 rhs1
                        in
                     [TERM (ctx_u, sol)]
                  in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16312 = quasi_pattern env1 lhs1  in
                 match uu____16312 with
                 | FStar_Pervasives_Native.None  ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs,uu____16346) ->
                     let uu____16351 = lhs1  in
                     (match uu____16351 with
                      | Flex (t_lhs,ctx_u,args) ->
                          let uu____16366 = occurs_check ctx_u rhs1  in
                          (match uu____16366 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16417 =
                                   let uu____16425 =
                                     let uu____16427 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16427
                                      in
                                   FStar_Util.Inl uu____16425  in
                                 (uu____16417, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs)
                                     in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1
                                     in
                                  let uu____16455 =
                                    let uu____16457 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs
                                       in
                                    Prims.op_Negation uu____16457  in
                                  if uu____16455
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16484 =
                                       let uu____16492 =
                                         mk_solution env1 lhs1 bs rhs1  in
                                       FStar_Util.Inr uu____16492  in
                                     let uu____16498 =
                                       restrict_all_uvars ctx_u uvars wl1  in
                                     (uu____16484, uu____16498)))))
                  in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16542 = FStar_Syntax_Util.head_and_args rhs1  in
                 match uu____16542 with
                 | (rhs_hd,args) ->
                     let uu____16585 = FStar_Util.prefix args  in
                     (match uu____16585 with
                      | (args_rhs,last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              rhs1.FStar_Syntax_Syntax.pos
                             in
                          let uu____16655 = lhs1  in
                          (match uu____16655 with
                           | Flex (t_lhs,u_lhs,_lhs_args) ->
                               let uu____16659 =
                                 let uu____16670 =
                                   let uu____16677 =
                                     let uu____16680 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16680
                                      in
                                   copy_uvar u_lhs [] uu____16677 wl1  in
                                 match uu____16670 with
                                 | (uu____16707,t_last_arg,wl2) ->
                                     let uu____16710 =
                                       let uu____16717 =
                                         let uu____16718 =
                                           let uu____16727 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg
                                              in
                                           [uu____16727]  in
                                         FStar_List.append bs_lhs uu____16718
                                          in
                                       copy_uvar u_lhs uu____16717 t_res_lhs
                                         wl2
                                        in
                                     (match uu____16710 with
                                      | (uu____16762,lhs',wl3) ->
                                          let uu____16765 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3
                                             in
                                          (match uu____16765 with
                                           | (uu____16782,lhs'_last_arg,wl4)
                                               -> (lhs', lhs'_last_arg, wl4)))
                                  in
                               (match uu____16659 with
                                | (lhs',lhs'_last_arg,wl2) ->
                                    let sol =
                                      let uu____16803 =
                                        let uu____16804 =
                                          let uu____16809 =
                                            let uu____16810 =
                                              let uu____16813 =
                                                let uu____16814 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    lhs'_last_arg
                                                   in
                                                [uu____16814]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                lhs' uu____16813
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16810
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16809)  in
                                        TERM uu____16804  in
                                      [uu____16803]  in
                                    let uu____16839 =
                                      let uu____16846 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs"
                                         in
                                      match uu____16846 with
                                      | (p1,wl3) ->
                                          let uu____16866 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs"
                                             in
                                          (match uu____16866 with
                                           | (p2,wl4) -> ([p1; p2], wl4))
                                       in
                                    (match uu____16839 with
                                     | (sub_probs,wl3) ->
                                         let uu____16898 =
                                           let uu____16899 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16899  in
                                         solve env1 uu____16898))))
                  in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16933 = FStar_Syntax_Util.head_and_args rhs2  in
                   match uu____16933 with
                   | (uu____16951,args) ->
                       (match args with | [] -> false | uu____16987 -> true)
                    in
                 let is_arrow rhs2 =
                   let uu____17006 =
                     let uu____17007 = FStar_Syntax_Subst.compress rhs2  in
                     uu____17007.FStar_Syntax_Syntax.n  in
                   match uu____17006 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____17011 -> true
                   | uu____17027 -> false  in
                 let uu____17029 = quasi_pattern env1 lhs1  in
                 match uu____17029 with
                 | FStar_Pervasives_Native.None  ->
                     let msg =
                       mklstr
                         (fun uu____17048  ->
                            let uu____17049 = prob_to_string env1 orig1  in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____17049)
                        in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                     let uu____17058 = is_app rhs1  in
                     if uu____17058
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____17063 = is_arrow rhs1  in
                        if uu____17063
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu____17076  ->
                                  let uu____17077 = prob_to_string env1 orig1
                                     in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____17077)
                              in
                           giveup_or_defer env1 orig1 wl1 msg))
                  in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB  ->
                   if wl.defer_ok
                   then
                     let uu____17081 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____17081
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV  ->
                   if wl.defer_ok
                   then
                     let uu____17087 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____17087
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ  ->
                   let uu____17092 = lhs  in
                   (match uu____17092 with
                    | Flex (_t1,ctx_uv,args_lhs) ->
                        let uu____17096 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs
                           in
                        (match uu____17096 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs  in
                             let names_to_string1 fvs =
                               let uu____17114 =
                                 let uu____17118 =
                                   FStar_Util.set_elements fvs  in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____17118
                                  in
                               FStar_All.pipe_right uu____17114
                                 (FStar_String.concat ", ")
                                in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders)
                                in
                             let fvs2 = FStar_Syntax_Free.names rhs1  in
                             let uu____17139 = occurs_check ctx_uv rhs1  in
                             (match uu____17139 with
                              | (uvars,occurs_ok,msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17168 =
                                      let uu____17169 =
                                        let uu____17171 =
                                          FStar_Option.get msg  in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17171
                                         in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17169
                                       in
                                    giveup_or_defer env orig wl uu____17168
                                  else
                                    (let uu____17179 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1
                                        in
                                     if uu____17179
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1
                                          in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars wl
                                          in
                                       let uu____17186 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1
                                          in
                                       solve env uu____17186
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            mklstr
                                              (fun uu____17202  ->
                                                 let uu____17203 =
                                                   names_to_string1 fvs2  in
                                                 let uu____17205 =
                                                   names_to_string1 fvs1  in
                                                 let uu____17207 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders)
                                                    in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17203 uu____17205
                                                   uu____17207)
                                             in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17219 ->
                             if wl.defer_ok
                             then
                               let uu____17223 =
                                 FStar_Thunk.mkv "Not a pattern"  in
                               giveup_or_defer env orig wl uu____17223
                             else
                               (let uu____17228 =
                                  try_quasi_pattern orig env wl lhs rhs  in
                                match uu____17228 with
                                | (FStar_Util.Inr sol,wl1) ->
                                    let uu____17254 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17254
                                | (FStar_Util.Inl msg,uu____17256) ->
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
                  let uu____17274 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17274
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____17280 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17280
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17285 =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs)
                   in
                if uu____17285
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
                    (let uu____17292 =
                       FStar_Thunk.mkv "flex-flex non-pattern"  in
                     giveup_or_defer env orig wl uu____17292)
                  else
                    (let uu____17297 =
                       let uu____17314 = quasi_pattern env lhs  in
                       let uu____17321 = quasi_pattern env rhs  in
                       (uu____17314, uu____17321)  in
                     match uu____17297 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                        (binders_rhs,t_res_rhs)) ->
                         let uu____17364 = lhs  in
                         (match uu____17364 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17365;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17367;_},u_lhs,uu____17369)
                              ->
                              let uu____17372 = rhs  in
                              (match uu____17372 with
                               | Flex (uu____17373,u_rhs,uu____17375) ->
                                   let uu____17376 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs)
                                      in
                                   if uu____17376
                                   then
                                     let uu____17383 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl
                                        in
                                     solve env uu____17383
                                   else
                                     (let uu____17386 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      match uu____17386 with
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
                                          let uu____17418 =
                                            let uu____17425 =
                                              let uu____17428 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs
                                                 in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17428
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
                                              uu____17425
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None
                                             in
                                          (match uu____17418 with
                                           | (uu____17434,w,wl1) ->
                                               let w_app =
                                                 let uu____17438 =
                                                   FStar_List.map
                                                     (fun uu____17449  ->
                                                        match uu____17449
                                                        with
                                                        | (z,uu____17457) ->
                                                            let uu____17462 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____17462) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____17438
                                                   w.FStar_Syntax_Syntax.pos
                                                  in
                                               ((let uu____17464 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17464
                                                 then
                                                   let uu____17469 =
                                                     let uu____17473 =
                                                       flex_t_to_string lhs
                                                        in
                                                     let uu____17475 =
                                                       let uu____17479 =
                                                         flex_t_to_string rhs
                                                          in
                                                       let uu____17481 =
                                                         let uu____17485 =
                                                           term_to_string w
                                                            in
                                                         let uu____17487 =
                                                           let uu____17491 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs)
                                                              in
                                                           let uu____17500 =
                                                             let uu____17504
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                in
                                                             let uu____17513
                                                               =
                                                               let uu____17517
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs
                                                                  in
                                                               [uu____17517]
                                                                in
                                                             uu____17504 ::
                                                               uu____17513
                                                              in
                                                           uu____17491 ::
                                                             uu____17500
                                                            in
                                                         uu____17485 ::
                                                           uu____17487
                                                          in
                                                       uu____17479 ::
                                                         uu____17481
                                                        in
                                                     uu____17473 ::
                                                       uu____17475
                                                      in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17469
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17534 =
                                                       let uu____17539 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs))
                                                          in
                                                       (u_lhs, uu____17539)
                                                        in
                                                     TERM uu____17534  in
                                                   let uu____17540 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                      in
                                                   if uu____17540
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17548 =
                                                          let uu____17553 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_rhs,
                                                            uu____17553)
                                                           in
                                                        TERM uu____17548  in
                                                      [s1; s2])
                                                    in
                                                 let uu____17554 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1
                                                    in
                                                 solve env uu____17554))))))
                     | uu____17555 ->
                         let uu____17572 =
                           FStar_Thunk.mkv "flex-flex: non-patterns"  in
                         giveup_or_defer env orig wl uu____17572)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17626 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17626
            then
              let uu____17631 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17633 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17635 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17637 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17631 uu____17633 uu____17635 uu____17637
            else ());
           (let uu____17648 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17648 with
            | (head1,args1) ->
                let uu____17691 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17691 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17761 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17761 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17766 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17766)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17787 =
                         mklstr
                           (fun uu____17798  ->
                              let uu____17799 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17801 = args_to_string args1  in
                              let uu____17805 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17807 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17799 uu____17801 uu____17805
                                uu____17807)
                          in
                       giveup env1 uu____17787 orig
                     else
                       (let uu____17814 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17819 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17819 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17814
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2610_17823 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2610_17823.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2610_17823.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2610_17823.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2610_17823.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2610_17823.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2610_17823.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2610_17823.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2610_17823.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17833 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17833
                                    else solve env1 wl2))
                        else
                          (let uu____17838 = base_and_refinement env1 t1  in
                           match uu____17838 with
                           | (base1,refinement1) ->
                               let uu____17863 = base_and_refinement env1 t2
                                  in
                               (match uu____17863 with
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
                                           let uu____18028 =
                                             FStar_List.fold_right
                                               (fun uu____18068  ->
                                                  fun uu____18069  ->
                                                    match (uu____18068,
                                                            uu____18069)
                                                    with
                                                    | (((a1,uu____18121),
                                                        (a2,uu____18123)),
                                                       (probs,wl3)) ->
                                                        let uu____18172 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18172
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____18028 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18215 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18215
                                                 then
                                                   let uu____18220 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18220
                                                 else ());
                                                (let uu____18226 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18226
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
                                                    (let uu____18253 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18253 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18269 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18269
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18277 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18277))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18302 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18302 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18318 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18318
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18326 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18326)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18354 =
                                           match uu____18354 with
                                           | (prob,reason) ->
                                               ((let uu____18371 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18371
                                                 then
                                                   let uu____18376 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18378 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____18376 uu____18378
                                                 else ());
                                                (let uu____18384 =
                                                   let uu____18393 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18396 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18393, uu____18396)
                                                    in
                                                 match uu____18384 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18409 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18409 with
                                                      | (head1',uu____18427)
                                                          ->
                                                          let uu____18452 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18452
                                                           with
                                                           | (head2',uu____18470)
                                                               ->
                                                               let uu____18495
                                                                 =
                                                                 let uu____18500
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18501
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18500,
                                                                   uu____18501)
                                                                  in
                                                               (match uu____18495
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18503
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18503
                                                                    then
                                                                    let uu____18508
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18510
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18512
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18514
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18508
                                                                    uu____18510
                                                                    uu____18512
                                                                    uu____18514
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18519
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2698_18527
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2698_18527.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2698_18527.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2698_18527.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2698_18527.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2698_18527.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2698_18527.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2698_18527.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2698_18527.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18529
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18529
                                                                    then
                                                                    let uu____18534
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18534
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18539 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18551 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18551 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18559 =
                                             let uu____18560 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18560.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18559 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18565 -> false  in
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
                                          | uu____18568 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18571 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2718_18607 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2718_18607.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2718_18607.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2718_18607.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2718_18607.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2718_18607.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2718_18607.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2718_18607.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2718_18607.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18683 = destruct_flex_t scrutinee wl1  in
             match uu____18683 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____18694 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18694 with
                  | (xs,pat_term,uu____18710,uu____18711) ->
                      let uu____18716 =
                        FStar_List.fold_left
                          (fun uu____18739  ->
                             fun x  ->
                               match uu____18739 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18760 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18760 with
                                    | (uu____18779,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18716 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18800 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18800 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2759_18817 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2759_18817.wl_deferred_to_tac);
                                    ctr = (uu___2759_18817.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2759_18817.umax_heuristic_ok);
                                    tcenv = (uu___2759_18817.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2759_18817.repr_subcomp_allowed)
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18828 = solve env1 wl'  in
                                (match uu____18828 with
                                 | Success (uu____18831,defer_to_tac,imps) ->
                                     let wl'1 =
                                       let uu___2768_18835 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2768_18835.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2768_18835.wl_deferred_to_tac);
                                         ctr = (uu___2768_18835.ctr);
                                         defer_ok =
                                           (uu___2768_18835.defer_ok);
                                         smt_ok = (uu___2768_18835.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2768_18835.umax_heuristic_ok);
                                         tcenv = (uu___2768_18835.tcenv);
                                         wl_implicits =
                                           (uu___2768_18835.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2768_18835.repr_subcomp_allowed)
                                       }  in
                                     let uu____18836 = solve env1 wl'1  in
                                     (match uu____18836 with
                                      | Success
                                          (uu____18839,defer_to_tac',imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18843 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps')
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____18843))
                                      | Failed uu____18849 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18855 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18878 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18878
                 then
                   let uu____18883 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18885 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18883 uu____18885
                 else ());
                (let uu____18890 =
                   let uu____18911 =
                     let uu____18920 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18920)  in
                   let uu____18927 =
                     let uu____18936 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18936)  in
                   (uu____18911, uu____18927)  in
                 match uu____18890 with
                 | ((uu____18966,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18969;
                                   FStar_Syntax_Syntax.vars = uu____18970;_}),
                    (s,t)) ->
                     let uu____19041 =
                       let uu____19043 = is_flex scrutinee  in
                       Prims.op_Negation uu____19043  in
                     if uu____19041
                     then
                       ((let uu____19054 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19054
                         then
                           let uu____19059 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19059
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19078 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19078
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19093 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19093
                           then
                             let uu____19098 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19100 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19098 uu____19100
                           else ());
                          (let pat_discriminates uu___26_19125 =
                             match uu___26_19125 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19141;
                                  FStar_Syntax_Syntax.p = uu____19142;_},FStar_Pervasives_Native.None
                                ,uu____19143) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19157;
                                  FStar_Syntax_Syntax.p = uu____19158;_},FStar_Pervasives_Native.None
                                ,uu____19159) -> true
                             | uu____19186 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19289 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19289 with
                                       | (uu____19291,uu____19292,t') ->
                                           let uu____19310 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19310 with
                                            | (FullMatch ,uu____19322) ->
                                                true
                                            | (HeadMatch
                                               uu____19336,uu____19337) ->
                                                true
                                            | uu____19352 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19389 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19389
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19400 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19400 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19488,uu____19489) ->
                                       branches1
                                   | uu____19634 -> branches  in
                                 let uu____19689 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19698 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19698 with
                                        | (p,uu____19702,uu____19703) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19732  ->
                                      FStar_Util.Inr uu____19732) uu____19689))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19762 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19762 with
                                | (p,uu____19771,e) ->
                                    ((let uu____19790 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19790
                                      then
                                        let uu____19795 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19797 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19795 uu____19797
                                      else ());
                                     (let uu____19802 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19817  ->
                                           FStar_Util.Inr uu____19817)
                                        uu____19802)))))
                 | ((s,t),(uu____19820,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19823;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19824;_}))
                     ->
                     let uu____19893 =
                       let uu____19895 = is_flex scrutinee  in
                       Prims.op_Negation uu____19895  in
                     if uu____19893
                     then
                       ((let uu____19906 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19906
                         then
                           let uu____19911 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19911
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19930 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19930
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19945 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19945
                           then
                             let uu____19950 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19952 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19950 uu____19952
                           else ());
                          (let pat_discriminates uu___26_19977 =
                             match uu___26_19977 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19993;
                                  FStar_Syntax_Syntax.p = uu____19994;_},FStar_Pervasives_Native.None
                                ,uu____19995) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____20009;
                                  FStar_Syntax_Syntax.p = uu____20010;_},FStar_Pervasives_Native.None
                                ,uu____20011) -> true
                             | uu____20038 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20141 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20141 with
                                       | (uu____20143,uu____20144,t') ->
                                           let uu____20162 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20162 with
                                            | (FullMatch ,uu____20174) ->
                                                true
                                            | (HeadMatch
                                               uu____20188,uu____20189) ->
                                                true
                                            | uu____20204 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20241 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20241
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20252 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20252 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20340,uu____20341) ->
                                       branches1
                                   | uu____20486 -> branches  in
                                 let uu____20541 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20550 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20550 with
                                        | (p,uu____20554,uu____20555) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____20584  ->
                                      FStar_Util.Inr uu____20584) uu____20541))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20614 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20614 with
                                | (p,uu____20623,e) ->
                                    ((let uu____20642 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20642
                                      then
                                        let uu____20647 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20649 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20647 uu____20649
                                      else ());
                                     (let uu____20654 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____20669  ->
                                           FStar_Util.Inr uu____20669)
                                        uu____20654)))))
                 | uu____20670 ->
                     ((let uu____20692 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20692
                       then
                         let uu____20697 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20699 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20697 uu____20699
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20745 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20745
            then
              let uu____20750 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20752 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20754 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20756 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20750 uu____20752 uu____20754 uu____20756
            else ());
           (let uu____20761 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20761 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20792,uu____20793) ->
                     let rec may_relate head =
                       let uu____20821 =
                         let uu____20822 = FStar_Syntax_Subst.compress head
                            in
                         uu____20822.FStar_Syntax_Syntax.n  in
                       match uu____20821 with
                       | FStar_Syntax_Syntax.Tm_name uu____20826 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20828 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20853 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20853 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20855 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20858
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20859 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20862,uu____20863) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20905) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20911) ->
                           may_relate t
                       | uu____20916 -> false  in
                     let uu____20918 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20918 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20931 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20931
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20941 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20941
                          then
                            let uu____20944 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20944 with
                             | (guard,wl2) ->
                                 let uu____20951 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20951)
                          else
                            (let uu____20954 =
                               mklstr
                                 (fun uu____20965  ->
                                    let uu____20966 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20968 =
                                      let uu____20970 =
                                        let uu____20974 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20974
                                          (fun x  ->
                                             let uu____20981 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20981)
                                         in
                                      FStar_Util.dflt "" uu____20970  in
                                    let uu____20986 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20988 =
                                      let uu____20990 =
                                        let uu____20994 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20994
                                          (fun x  ->
                                             let uu____21001 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____21001)
                                         in
                                      FStar_Util.dflt "" uu____20990  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20966 uu____20968 uu____20986
                                      uu____20988)
                                in
                             giveup env1 uu____20954 orig))
                 | (HeadMatch (true ),uu____21007) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____21022 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____21022 with
                        | (guard,wl2) ->
                            let uu____21029 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____21029)
                     else
                       (let uu____21032 =
                          mklstr
                            (fun uu____21039  ->
                               let uu____21040 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____21042 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____21040 uu____21042)
                           in
                        giveup env1 uu____21032 orig)
                 | (uu____21045,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2950_21059 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2950_21059.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2950_21059.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2950_21059.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2950_21059.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2950_21059.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2950_21059.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2950_21059.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2950_21059.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____21086 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____21086
          then
            let uu____21089 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____21089
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____21095 =
                let uu____21098 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21098  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____21095 t1);
             (let uu____21117 =
                let uu____21120 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21120  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____21117 t2);
             (let uu____21139 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____21139
              then
                let uu____21143 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____21145 =
                  let uu____21147 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____21149 =
                    let uu____21151 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____21151  in
                  Prims.op_Hat uu____21147 uu____21149  in
                let uu____21154 =
                  let uu____21156 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____21158 =
                    let uu____21160 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____21160  in
                  Prims.op_Hat uu____21156 uu____21158  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21143 uu____21145 uu____21154
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21167,uu____21168) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21184,FStar_Syntax_Syntax.Tm_delayed uu____21185) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21201,uu____21202) ->
                  let uu____21229 =
                    let uu___2981_21230 = problem  in
                    let uu____21231 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2981_21230.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21231;
                      FStar_TypeChecker_Common.relation =
                        (uu___2981_21230.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2981_21230.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2981_21230.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2981_21230.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2981_21230.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2981_21230.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2981_21230.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2981_21230.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21229 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21232,uu____21233) ->
                  let uu____21240 =
                    let uu___2987_21241 = problem  in
                    let uu____21242 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2987_21241.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21242;
                      FStar_TypeChecker_Common.relation =
                        (uu___2987_21241.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2987_21241.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2987_21241.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2987_21241.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2987_21241.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2987_21241.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2987_21241.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2987_21241.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21240 wl
              | (uu____21243,FStar_Syntax_Syntax.Tm_ascribed uu____21244) ->
                  let uu____21271 =
                    let uu___2993_21272 = problem  in
                    let uu____21273 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2993_21272.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2993_21272.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2993_21272.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21273;
                      FStar_TypeChecker_Common.element =
                        (uu___2993_21272.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2993_21272.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2993_21272.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2993_21272.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2993_21272.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2993_21272.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21271 wl
              | (uu____21274,FStar_Syntax_Syntax.Tm_meta uu____21275) ->
                  let uu____21282 =
                    let uu___2999_21283 = problem  in
                    let uu____21284 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2999_21283.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2999_21283.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2999_21283.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21284;
                      FStar_TypeChecker_Common.element =
                        (uu___2999_21283.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2999_21283.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2999_21283.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2999_21283.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2999_21283.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2999_21283.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21282 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21286),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21288)) ->
                  let uu____21297 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21297
              | (FStar_Syntax_Syntax.Tm_bvar uu____21298,uu____21299) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21301,FStar_Syntax_Syntax.Tm_bvar uu____21302) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___27_21372 =
                    match uu___27_21372 with
                    | [] -> c
                    | bs ->
                        let uu____21400 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21400
                     in
                  let uu____21411 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21411 with
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
                                    let uu____21560 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21560
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
                  let mk_t t l uu___28_21649 =
                    match uu___28_21649 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21691 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21691 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21836 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21837 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21836
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21837 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21839,uu____21840) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21871 -> true
                    | uu____21891 -> false  in
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
                      (let uu____21951 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3101_21959 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3101_21959.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3101_21959.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3101_21959.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3101_21959.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3101_21959.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3101_21959.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3101_21959.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3101_21959.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3101_21959.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3101_21959.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3101_21959.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3101_21959.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3101_21959.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3101_21959.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3101_21959.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3101_21959.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3101_21959.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3101_21959.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3101_21959.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3101_21959.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3101_21959.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3101_21959.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3101_21959.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3101_21959.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3101_21959.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3101_21959.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3101_21959.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3101_21959.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3101_21959.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3101_21959.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3101_21959.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3101_21959.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3101_21959.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3101_21959.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3101_21959.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3101_21959.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3101_21959.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3101_21959.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3101_21959.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3101_21959.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3101_21959.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3101_21959.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3101_21959.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3101_21959.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____21951 with
                       | (uu____21964,ty,uu____21966) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21975 =
                                 let uu____21976 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21976.FStar_Syntax_Syntax.n  in
                               match uu____21975 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21979 ->
                                   let uu____21986 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21986
                               | uu____21987 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21990 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21990
                             then
                               let uu____21995 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21997 =
                                 let uu____21999 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21999
                                  in
                               let uu____22000 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21995 uu____21997 uu____22000
                             else ());
                            r1))
                     in
                  let uu____22005 =
                    let uu____22022 = maybe_eta t1  in
                    let uu____22029 = maybe_eta t2  in
                    (uu____22022, uu____22029)  in
                  (match uu____22005 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3122_22071 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3122_22071.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3122_22071.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3122_22071.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3122_22071.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3122_22071.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3122_22071.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3122_22071.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3122_22071.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22092 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22092
                       then
                         let uu____22095 = destruct_flex_t not_abs wl  in
                         (match uu____22095 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3139_22112 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3139_22112.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3139_22112.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3139_22112.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3139_22112.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3139_22112.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3139_22112.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3139_22112.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3139_22112.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22115 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22115 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22138 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22138
                       then
                         let uu____22141 = destruct_flex_t not_abs wl  in
                         (match uu____22141 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3139_22158 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3139_22158.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3139_22158.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3139_22158.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3139_22158.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3139_22158.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3139_22158.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3139_22158.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3139_22158.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22161 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22161 orig))
                   | uu____22164 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22182,FStar_Syntax_Syntax.Tm_abs uu____22183) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22214 -> true
                    | uu____22234 -> false  in
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
                      (let uu____22294 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3101_22302 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3101_22302.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3101_22302.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3101_22302.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3101_22302.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3101_22302.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3101_22302.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3101_22302.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3101_22302.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3101_22302.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3101_22302.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3101_22302.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3101_22302.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3101_22302.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3101_22302.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3101_22302.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3101_22302.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3101_22302.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3101_22302.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3101_22302.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3101_22302.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3101_22302.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3101_22302.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3101_22302.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3101_22302.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3101_22302.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3101_22302.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3101_22302.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3101_22302.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3101_22302.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3101_22302.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3101_22302.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3101_22302.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3101_22302.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3101_22302.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3101_22302.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3101_22302.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3101_22302.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3101_22302.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3101_22302.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3101_22302.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3101_22302.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3101_22302.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3101_22302.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3101_22302.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____22294 with
                       | (uu____22307,ty,uu____22309) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22318 =
                                 let uu____22319 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22319.FStar_Syntax_Syntax.n  in
                               match uu____22318 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22322 ->
                                   let uu____22329 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22329
                               | uu____22330 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22333 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22333
                             then
                               let uu____22338 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22340 =
                                 let uu____22342 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22342
                                  in
                               let uu____22343 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22338 uu____22340 uu____22343
                             else ());
                            r1))
                     in
                  let uu____22348 =
                    let uu____22365 = maybe_eta t1  in
                    let uu____22372 = maybe_eta t2  in
                    (uu____22365, uu____22372)  in
                  (match uu____22348 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3122_22414 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3122_22414.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3122_22414.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3122_22414.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3122_22414.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3122_22414.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3122_22414.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3122_22414.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3122_22414.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22435 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22435
                       then
                         let uu____22438 = destruct_flex_t not_abs wl  in
                         (match uu____22438 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3139_22455 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3139_22455.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3139_22455.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3139_22455.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3139_22455.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3139_22455.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3139_22455.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3139_22455.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3139_22455.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22458 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22458 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22481 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22481
                       then
                         let uu____22484 = destruct_flex_t not_abs wl  in
                         (match uu____22484 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3139_22501 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3139_22501.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3139_22501.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3139_22501.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3139_22501.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3139_22501.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3139_22501.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3139_22501.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3139_22501.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22504 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22504 orig))
                   | uu____22507 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22537 =
                    let uu____22542 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22542 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3162_22570 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3162_22570.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3162_22570.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3164_22572 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3164_22572.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3164_22572.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22573,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3162_22588 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3162_22588.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3162_22588.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3164_22590 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3164_22590.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3164_22590.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22591 -> (x1, x2)  in
                  (match uu____22537 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22610 = as_refinement false env t11  in
                       (match uu____22610 with
                        | (x12,phi11) ->
                            let uu____22618 = as_refinement false env t21  in
                            (match uu____22618 with
                             | (x22,phi21) ->
                                 ((let uu____22627 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22627
                                   then
                                     ((let uu____22632 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22634 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22636 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22632
                                         uu____22634 uu____22636);
                                      (let uu____22639 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22641 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22643 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22639
                                         uu____22641 uu____22643))
                                   else ());
                                  (let uu____22648 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22648 with
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
                                         let uu____22719 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22719
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22731 =
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
                                         (let uu____22744 =
                                            let uu____22747 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22747
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22744
                                            (p_guard base_prob));
                                         (let uu____22766 =
                                            let uu____22769 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22769
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22766
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22788 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22788)
                                          in
                                       let has_uvars =
                                         (let uu____22793 =
                                            let uu____22795 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22795
                                             in
                                          Prims.op_Negation uu____22793) ||
                                           (let uu____22799 =
                                              let uu____22801 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22801
                                               in
                                            Prims.op_Negation uu____22799)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22805 =
                                           let uu____22810 =
                                             let uu____22819 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22819]  in
                                           mk_t_problem wl1 uu____22810 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22805 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22842 =
                                                solve env1
                                                  (let uu___3207_22844 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3207_22844.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3207_22844.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3207_22844.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3207_22844.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3207_22844.tcenv);
                                                     wl_implicits =
                                                       (uu___3207_22844.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3207_22844.repr_subcomp_allowed)
                                                   })
                                                 in
                                              (match uu____22842 with
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
                                                   (uu____22859,defer_to_tac,uu____22861)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22866 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22866
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3223_22875 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3223_22875.attempting);
                                                         wl_deferred =
                                                           (uu___3223_22875.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3223_22875.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3223_22875.defer_ok);
                                                         smt_ok =
                                                           (uu___3223_22875.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3223_22875.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3223_22875.tcenv);
                                                         wl_implicits =
                                                           (uu___3223_22875.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3223_22875.repr_subcomp_allowed)
                                                       }  in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac []
                                                        in
                                                     let uu____22878 =
                                                       attempt [base_prob]
                                                         wl5
                                                        in
                                                     solve env1 uu____22878))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22881,FStar_Syntax_Syntax.Tm_uvar uu____22882) ->
                  let uu____22907 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22907 with
                   | (t11,wl1) ->
                       let uu____22914 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22914 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22923;
                    FStar_Syntax_Syntax.pos = uu____22924;
                    FStar_Syntax_Syntax.vars = uu____22925;_},uu____22926),FStar_Syntax_Syntax.Tm_uvar
                 uu____22927) ->
                  let uu____22976 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22976 with
                   | (t11,wl1) ->
                       let uu____22983 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22983 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22992,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22993;
                    FStar_Syntax_Syntax.pos = uu____22994;
                    FStar_Syntax_Syntax.vars = uu____22995;_},uu____22996))
                  ->
                  let uu____23045 = ensure_no_uvar_subst t1 wl  in
                  (match uu____23045 with
                   | (t11,wl1) ->
                       let uu____23052 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____23052 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23061;
                    FStar_Syntax_Syntax.pos = uu____23062;
                    FStar_Syntax_Syntax.vars = uu____23063;_},uu____23064),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23065;
                    FStar_Syntax_Syntax.pos = uu____23066;
                    FStar_Syntax_Syntax.vars = uu____23067;_},uu____23068))
                  ->
                  let uu____23141 = ensure_no_uvar_subst t1 wl  in
                  (match uu____23141 with
                   | (t11,wl1) ->
                       let uu____23148 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____23148 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23157,uu____23158) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23171 = destruct_flex_t t1 wl  in
                  (match uu____23171 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23178;
                    FStar_Syntax_Syntax.pos = uu____23179;
                    FStar_Syntax_Syntax.vars = uu____23180;_},uu____23181),uu____23182)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23219 = destruct_flex_t t1 wl  in
                  (match uu____23219 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23226,FStar_Syntax_Syntax.Tm_uvar uu____23227) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23240,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23241;
                    FStar_Syntax_Syntax.pos = uu____23242;
                    FStar_Syntax_Syntax.vars = uu____23243;_},uu____23244))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23281,FStar_Syntax_Syntax.Tm_arrow uu____23282) ->
                  solve_t' env
                    (let uu___3326_23310 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3326_23310.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3326_23310.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3326_23310.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3326_23310.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3326_23310.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3326_23310.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3326_23310.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3326_23310.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3326_23310.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23311;
                    FStar_Syntax_Syntax.pos = uu____23312;
                    FStar_Syntax_Syntax.vars = uu____23313;_},uu____23314),FStar_Syntax_Syntax.Tm_arrow
                 uu____23315) ->
                  solve_t' env
                    (let uu___3326_23367 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3326_23367.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3326_23367.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3326_23367.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3326_23367.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3326_23367.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3326_23367.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3326_23367.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3326_23367.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3326_23367.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23368,FStar_Syntax_Syntax.Tm_uvar uu____23369) ->
                  let uu____23382 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23382
              | (uu____23383,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23384;
                    FStar_Syntax_Syntax.pos = uu____23385;
                    FStar_Syntax_Syntax.vars = uu____23386;_},uu____23387))
                  ->
                  let uu____23424 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23424
              | (FStar_Syntax_Syntax.Tm_uvar uu____23425,uu____23426) ->
                  let uu____23439 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23439
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23440;
                    FStar_Syntax_Syntax.pos = uu____23441;
                    FStar_Syntax_Syntax.vars = uu____23442;_},uu____23443),uu____23444)
                  ->
                  let uu____23481 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23481
              | (FStar_Syntax_Syntax.Tm_refine uu____23482,uu____23483) ->
                  let t21 =
                    let uu____23491 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23491  in
                  solve_t env
                    (let uu___3361_23517 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3361_23517.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3361_23517.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3361_23517.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3361_23517.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3361_23517.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3361_23517.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3361_23517.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3361_23517.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3361_23517.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23518,FStar_Syntax_Syntax.Tm_refine uu____23519) ->
                  let t11 =
                    let uu____23527 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23527  in
                  solve_t env
                    (let uu___3368_23553 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3368_23553.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3368_23553.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3368_23553.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3368_23553.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3368_23553.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3368_23553.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3368_23553.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3368_23553.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3368_23553.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23635 =
                    let uu____23636 = guard_of_prob env wl problem t1 t2  in
                    match uu____23636 with
                    | (guard,wl1) ->
                        let uu____23643 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23643
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23862 = br1  in
                        (match uu____23862 with
                         | (p1,w1,uu____23891) ->
                             let uu____23908 = br2  in
                             (match uu____23908 with
                              | (p2,w2,uu____23931) ->
                                  let uu____23936 =
                                    let uu____23938 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23938  in
                                  if uu____23936
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23965 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23965 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____24002 = br2  in
                                         (match uu____24002 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____24035 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____24035
                                                 in
                                              let uu____24040 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____24071,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____24092) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____24151 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____24151 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____24040
                                                (fun uu____24223  ->
                                                   match uu____24223 with
                                                   | (wprobs,wl2) ->
                                                       let uu____24260 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____24260
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24281
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24281
                                                              then
                                                                let uu____24286
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24288
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24286
                                                                  uu____24288
                                                              else ());
                                                             (let uu____24294
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24294
                                                                (fun
                                                                   uu____24330
                                                                    ->
                                                                   match uu____24330
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
                    | uu____24459 -> FStar_Pervasives_Native.None  in
                  let uu____24500 = solve_branches wl brs1 brs2  in
                  (match uu____24500 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24526 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24526 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24553 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24553 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24587 =
                                FStar_List.map
                                  (fun uu____24599  ->
                                     match uu____24599 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24587  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24608 =
                              let uu____24609 =
                                let uu____24610 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24610
                                  (let uu___3467_24618 = wl3  in
                                   {
                                     attempting =
                                       (uu___3467_24618.attempting);
                                     wl_deferred =
                                       (uu___3467_24618.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3467_24618.wl_deferred_to_tac);
                                     ctr = (uu___3467_24618.ctr);
                                     defer_ok = (uu___3467_24618.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3467_24618.umax_heuristic_ok);
                                     tcenv = (uu___3467_24618.tcenv);
                                     wl_implicits =
                                       (uu___3467_24618.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3467_24618.repr_subcomp_allowed)
                                   })
                                 in
                              solve env uu____24609  in
                            (match uu____24608 with
                             | Success (ds,ds',imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24624 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24633 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24633 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24636,uu____24637) ->
                  let head1 =
                    let uu____24661 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24661
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24707 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24707
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24753 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24753
                    then
                      let uu____24757 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24759 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24761 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24757 uu____24759 uu____24761
                    else ());
                   (let no_free_uvars t =
                      (let uu____24775 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24775) &&
                        (let uu____24779 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24779)
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
                      let uu____24798 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24798 = FStar_Syntax_Util.Equal  in
                    let uu____24799 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24799
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24803 = equal t1 t2  in
                         (if uu____24803
                          then
                            let uu____24806 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24806
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24811 =
                            let uu____24818 = equal t1 t2  in
                            if uu____24818
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24831 = mk_eq2 wl env orig t1 t2  in
                               match uu____24831 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24811 with
                          | (guard,wl1) ->
                              let uu____24852 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24852))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24855,uu____24856) ->
                  let head1 =
                    let uu____24864 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24864
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24910 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24910
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24956 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24956
                    then
                      let uu____24960 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24962 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24964 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24960 uu____24962 uu____24964
                    else ());
                   (let no_free_uvars t =
                      (let uu____24978 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24978) &&
                        (let uu____24982 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24982)
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
                      let uu____25001 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25001 = FStar_Syntax_Util.Equal  in
                    let uu____25002 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25002
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25006 = equal t1 t2  in
                         (if uu____25006
                          then
                            let uu____25009 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25009
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25014 =
                            let uu____25021 = equal t1 t2  in
                            if uu____25021
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25034 = mk_eq2 wl env orig t1 t2  in
                               match uu____25034 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25014 with
                          | (guard,wl1) ->
                              let uu____25055 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25055))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____25058,uu____25059) ->
                  let head1 =
                    let uu____25061 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25061
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25107 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25107
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25153 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25153
                    then
                      let uu____25157 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25159 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25161 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25157 uu____25159 uu____25161
                    else ());
                   (let no_free_uvars t =
                      (let uu____25175 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25175) &&
                        (let uu____25179 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25179)
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
                      let uu____25198 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25198 = FStar_Syntax_Util.Equal  in
                    let uu____25199 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25199
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25203 = equal t1 t2  in
                         (if uu____25203
                          then
                            let uu____25206 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25206
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25211 =
                            let uu____25218 = equal t1 t2  in
                            if uu____25218
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25231 = mk_eq2 wl env orig t1 t2  in
                               match uu____25231 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25211 with
                          | (guard,wl1) ->
                              let uu____25252 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25252))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25255,uu____25256) ->
                  let head1 =
                    let uu____25258 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25258
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25304 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25304
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25350 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25350
                    then
                      let uu____25354 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25356 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25358 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25354 uu____25356 uu____25358
                    else ());
                   (let no_free_uvars t =
                      (let uu____25372 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25372) &&
                        (let uu____25376 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25376)
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
                      let uu____25395 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25395 = FStar_Syntax_Util.Equal  in
                    let uu____25396 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25396
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25400 = equal t1 t2  in
                         (if uu____25400
                          then
                            let uu____25403 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25403
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25408 =
                            let uu____25415 = equal t1 t2  in
                            if uu____25415
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25428 = mk_eq2 wl env orig t1 t2  in
                               match uu____25428 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25408 with
                          | (guard,wl1) ->
                              let uu____25449 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25449))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25452,uu____25453) ->
                  let head1 =
                    let uu____25455 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25455
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25495 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25495
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25535 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25535
                    then
                      let uu____25539 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25541 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25543 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25539 uu____25541 uu____25543
                    else ());
                   (let no_free_uvars t =
                      (let uu____25557 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25557) &&
                        (let uu____25561 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25561)
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
                      let uu____25580 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25580 = FStar_Syntax_Util.Equal  in
                    let uu____25581 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25581
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25585 = equal t1 t2  in
                         (if uu____25585
                          then
                            let uu____25588 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25588
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25593 =
                            let uu____25600 = equal t1 t2  in
                            if uu____25600
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25613 = mk_eq2 wl env orig t1 t2  in
                               match uu____25613 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25593 with
                          | (guard,wl1) ->
                              let uu____25634 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25634))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25637,uu____25638) ->
                  let head1 =
                    let uu____25656 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25656
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25696 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25696
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25736 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25736
                    then
                      let uu____25740 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25742 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25744 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25740 uu____25742 uu____25744
                    else ());
                   (let no_free_uvars t =
                      (let uu____25758 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25758) &&
                        (let uu____25762 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25762)
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
                      let uu____25781 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25781 = FStar_Syntax_Util.Equal  in
                    let uu____25782 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25782
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25786 = equal t1 t2  in
                         (if uu____25786
                          then
                            let uu____25789 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25789
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25794 =
                            let uu____25801 = equal t1 t2  in
                            if uu____25801
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25814 = mk_eq2 wl env orig t1 t2  in
                               match uu____25814 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25794 with
                          | (guard,wl1) ->
                              let uu____25835 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25835))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25838,FStar_Syntax_Syntax.Tm_match uu____25839) ->
                  let head1 =
                    let uu____25863 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25863
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25903 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25903
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25943 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25943
                    then
                      let uu____25947 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25949 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25951 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25947 uu____25949 uu____25951
                    else ());
                   (let no_free_uvars t =
                      (let uu____25965 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25965) &&
                        (let uu____25969 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25969)
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
                      let uu____25988 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25988 = FStar_Syntax_Util.Equal  in
                    let uu____25989 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25989
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25993 = equal t1 t2  in
                         (if uu____25993
                          then
                            let uu____25996 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25996
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26001 =
                            let uu____26008 = equal t1 t2  in
                            if uu____26008
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26021 = mk_eq2 wl env orig t1 t2  in
                               match uu____26021 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26001 with
                          | (guard,wl1) ->
                              let uu____26042 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26042))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26045,FStar_Syntax_Syntax.Tm_uinst uu____26046) ->
                  let head1 =
                    let uu____26054 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26054
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26094 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26094
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26134 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26134
                    then
                      let uu____26138 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26140 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26142 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26138 uu____26140 uu____26142
                    else ());
                   (let no_free_uvars t =
                      (let uu____26156 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26156) &&
                        (let uu____26160 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26160)
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
                      let uu____26179 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26179 = FStar_Syntax_Util.Equal  in
                    let uu____26180 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26180
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26184 = equal t1 t2  in
                         (if uu____26184
                          then
                            let uu____26187 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26187
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26192 =
                            let uu____26199 = equal t1 t2  in
                            if uu____26199
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26212 = mk_eq2 wl env orig t1 t2  in
                               match uu____26212 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26192 with
                          | (guard,wl1) ->
                              let uu____26233 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26233))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26236,FStar_Syntax_Syntax.Tm_name uu____26237) ->
                  let head1 =
                    let uu____26239 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26239
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26279 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26279
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26319 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26319
                    then
                      let uu____26323 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26325 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26327 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26323 uu____26325 uu____26327
                    else ());
                   (let no_free_uvars t =
                      (let uu____26341 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26341) &&
                        (let uu____26345 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26345)
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
                      let uu____26364 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26364 = FStar_Syntax_Util.Equal  in
                    let uu____26365 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26365
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26369 = equal t1 t2  in
                         (if uu____26369
                          then
                            let uu____26372 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26372
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26377 =
                            let uu____26384 = equal t1 t2  in
                            if uu____26384
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26397 = mk_eq2 wl env orig t1 t2  in
                               match uu____26397 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26377 with
                          | (guard,wl1) ->
                              let uu____26418 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26418))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26421,FStar_Syntax_Syntax.Tm_constant uu____26422) ->
                  let head1 =
                    let uu____26424 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26424
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26464 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26464
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26504 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26504
                    then
                      let uu____26508 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26510 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26512 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26508 uu____26510 uu____26512
                    else ());
                   (let no_free_uvars t =
                      (let uu____26526 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26526) &&
                        (let uu____26530 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26530)
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
                      let uu____26549 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26549 = FStar_Syntax_Util.Equal  in
                    let uu____26550 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26550
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26554 = equal t1 t2  in
                         (if uu____26554
                          then
                            let uu____26557 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26557
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26562 =
                            let uu____26569 = equal t1 t2  in
                            if uu____26569
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26582 = mk_eq2 wl env orig t1 t2  in
                               match uu____26582 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26562 with
                          | (guard,wl1) ->
                              let uu____26603 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26603))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26606,FStar_Syntax_Syntax.Tm_fvar uu____26607) ->
                  let head1 =
                    let uu____26609 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26609
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26655 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26655
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26701 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26701
                    then
                      let uu____26705 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26707 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26709 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26705 uu____26707 uu____26709
                    else ());
                   (let no_free_uvars t =
                      (let uu____26723 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26723) &&
                        (let uu____26727 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26727)
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
                      let uu____26746 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26746 = FStar_Syntax_Util.Equal  in
                    let uu____26747 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26747
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26751 = equal t1 t2  in
                         (if uu____26751
                          then
                            let uu____26754 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26754
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26759 =
                            let uu____26766 = equal t1 t2  in
                            if uu____26766
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26779 = mk_eq2 wl env orig t1 t2  in
                               match uu____26779 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26759 with
                          | (guard,wl1) ->
                              let uu____26800 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26800))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26803,FStar_Syntax_Syntax.Tm_app uu____26804) ->
                  let head1 =
                    let uu____26822 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26822
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26862 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26862
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26902 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26902
                    then
                      let uu____26906 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26908 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26910 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26906 uu____26908 uu____26910
                    else ());
                   (let no_free_uvars t =
                      (let uu____26924 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26924) &&
                        (let uu____26928 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26928)
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
                      let uu____26947 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26947 = FStar_Syntax_Util.Equal  in
                    let uu____26948 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26948
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26952 = equal t1 t2  in
                         (if uu____26952
                          then
                            let uu____26955 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26955
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26960 =
                            let uu____26967 = equal t1 t2  in
                            if uu____26967
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26980 = mk_eq2 wl env orig t1 t2  in
                               match uu____26980 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26960 with
                          | (guard,wl1) ->
                              let uu____27001 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____27001))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____27004,FStar_Syntax_Syntax.Tm_let uu____27005) ->
                  let uu____27032 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____27032
                  then
                    let uu____27035 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____27035
                  else
                    (let uu____27038 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____27038 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____27041,uu____27042) ->
                  let uu____27056 =
                    let uu____27062 =
                      let uu____27064 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____27066 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____27068 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____27070 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27064 uu____27066 uu____27068 uu____27070
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27062)
                     in
                  FStar_Errors.raise_error uu____27056
                    t1.FStar_Syntax_Syntax.pos
              | (uu____27074,FStar_Syntax_Syntax.Tm_let uu____27075) ->
                  let uu____27089 =
                    let uu____27095 =
                      let uu____27097 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____27099 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____27101 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____27103 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27097 uu____27099 uu____27101 uu____27103
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27095)
                     in
                  FStar_Errors.raise_error uu____27089
                    t1.FStar_Syntax_Syntax.pos
              | uu____27107 ->
                  let uu____27112 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____27112 orig))))

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
          (let uu____27178 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____27178
           then
             let uu____27183 =
               let uu____27185 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____27185  in
             let uu____27186 =
               let uu____27188 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____27188  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27183 uu____27186
           else ());
          (let uu____27192 =
             let uu____27194 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____27194  in
           if uu____27192
           then
             let uu____27197 =
               mklstr
                 (fun uu____27204  ->
                    let uu____27205 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____27207 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27205 uu____27207)
                in
             giveup env uu____27197 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27229 =
                  mklstr
                    (fun uu____27236  ->
                       let uu____27237 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27239 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27237 uu____27239)
                   in
                giveup env uu____27229 orig)
             else
               (let uu____27244 =
                  FStar_List.fold_left2
                    (fun uu____27265  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27265 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27286 =
                                 let uu____27291 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27292 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27291
                                   FStar_TypeChecker_Common.EQ uu____27292
                                   "effect universes"
                                  in
                               (match uu____27286 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27244 with
                | (univ_sub_probs,wl1) ->
                    let uu____27312 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27312 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27320 =
                           FStar_List.fold_right2
                             (fun uu____27357  ->
                                fun uu____27358  ->
                                  fun uu____27359  ->
                                    match (uu____27357, uu____27358,
                                            uu____27359)
                                    with
                                    | ((a1,uu____27403),(a2,uu____27405),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27438 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27438 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27320 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27465 =
                                  let uu____27468 =
                                    let uu____27471 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27471
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27468
                                   in
                                FStar_List.append univ_sub_probs uu____27465
                                 in
                              let guard =
                                let guard =
                                  let uu____27493 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27493  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3620_27502 = wl3  in
                                {
                                  attempting = (uu___3620_27502.attempting);
                                  wl_deferred = (uu___3620_27502.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3620_27502.wl_deferred_to_tac);
                                  ctr = (uu___3620_27502.ctr);
                                  defer_ok = (uu___3620_27502.defer_ok);
                                  smt_ok = (uu___3620_27502.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3620_27502.umax_heuristic_ok);
                                  tcenv = (uu___3620_27502.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3620_27502.repr_subcomp_allowed)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27504 = attempt sub_probs wl5  in
                              solve env uu____27504))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____27522 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____27522
           then
             let uu____27527 =
               let uu____27529 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27529
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27531 =
               let uu____27533 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27533
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27527 uu____27531
           else ());
          (let uu____27538 =
             let uu____27543 =
               let uu____27548 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27548
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27543
               (fun uu____27565  ->
                  match uu____27565 with
                  | (c,g) ->
                      let uu____27576 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27576, g))
              in
           match uu____27538 with
           | (c12,g_lift) ->
               ((let uu____27580 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27580
                 then
                   let uu____27585 =
                     let uu____27587 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27587
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27589 =
                     let uu____27591 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27591
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27585 uu____27589
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3640_27601 = wl  in
                     {
                       attempting = (uu___3640_27601.attempting);
                       wl_deferred = (uu___3640_27601.wl_deferred);
                       wl_deferred_to_tac =
                         (uu___3640_27601.wl_deferred_to_tac);
                       ctr = (uu___3640_27601.ctr);
                       defer_ok = (uu___3640_27601.defer_ok);
                       smt_ok = (uu___3640_27601.smt_ok);
                       umax_heuristic_ok =
                         (uu___3640_27601.umax_heuristic_ok);
                       tcenv = (uu___3640_27601.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits);
                       repr_subcomp_allowed =
                         (uu___3640_27601.repr_subcomp_allowed)
                     }  in
                   let uu____27602 =
                     let rec is_uvar t =
                       let uu____27616 =
                         let uu____27617 = FStar_Syntax_Subst.compress t  in
                         uu____27617.FStar_Syntax_Syntax.n  in
                       match uu____27616 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27621 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27636) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27642) ->
                           is_uvar t1
                       | uu____27667 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27701  ->
                          fun uu____27702  ->
                            fun uu____27703  ->
                              match (uu____27701, uu____27702, uu____27703)
                              with
                              | ((a1,uu____27747),(a2,uu____27749),(is_sub_probs,wl2))
                                  ->
                                  let uu____27782 = is_uvar a1  in
                                  if uu____27782
                                  then
                                    ((let uu____27792 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27792
                                      then
                                        let uu____27797 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27799 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27797 uu____27799
                                      else ());
                                     (let uu____27804 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27804 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27602 with
                   | (is_sub_probs,wl2) ->
                       let uu____27832 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27832 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27840 =
                              let uu____27845 =
                                let uu____27846 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27846
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27845
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27840 with
                             | (uu____27853,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27864 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27866 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27864 s uu____27866
                                    in
                                 let uu____27869 =
                                   let uu____27898 =
                                     let uu____27899 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27899.FStar_Syntax_Syntax.n  in
                                   match uu____27898 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27959 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27959 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____28022 =
                                              let uu____28041 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____28041
                                                (fun uu____28145  ->
                                                   match uu____28145 with
                                                   | (l1,l2) ->
                                                       let uu____28218 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____28218))
                                               in
                                            (match uu____28022 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____28323 ->
                                       let uu____28324 =
                                         let uu____28330 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____28330)
                                          in
                                       FStar_Errors.raise_error uu____28324 r
                                    in
                                 (match uu____27869 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____28406 =
                                        let uu____28413 =
                                          let uu____28414 =
                                            let uu____28415 =
                                              let uu____28422 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____28422,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____28415
                                             in
                                          [uu____28414]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____28413
                                          (fun b  ->
                                             let uu____28438 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____28440 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28442 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____28438 uu____28440
                                               uu____28442) r
                                         in
                                      (match uu____28406 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____28452 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____28452
                                             then
                                               let uu____28457 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____28466 =
                                                          let uu____28468 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____28468
                                                           in
                                                        Prims.op_Hat s
                                                          uu____28466) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____28457
                                             else ());
                                            (let wl4 =
                                               let uu___3712_28476 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3712_28476.attempting);
                                                 wl_deferred =
                                                   (uu___3712_28476.wl_deferred);
                                                 wl_deferred_to_tac =
                                                   (uu___3712_28476.wl_deferred_to_tac);
                                                 ctr = (uu___3712_28476.ctr);
                                                 defer_ok =
                                                   (uu___3712_28476.defer_ok);
                                                 smt_ok =
                                                   (uu___3712_28476.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3712_28476.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3712_28476.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits);
                                                 repr_subcomp_allowed =
                                                   (uu___3712_28476.repr_subcomp_allowed)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____28501 =
                                                        let uu____28508 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____28508, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____28501) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____28525 =
                                               let f_sort_is =
                                                 let uu____28535 =
                                                   let uu____28536 =
                                                     let uu____28539 =
                                                       let uu____28540 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28540.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28539
                                                      in
                                                   uu____28536.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28535 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28551,uu____28552::is)
                                                     ->
                                                     let uu____28594 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28594
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28627 ->
                                                     let uu____28628 =
                                                       let uu____28634 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28634)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28628 r
                                                  in
                                               let uu____28640 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28675  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28675
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28696 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28696
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28640
                                                in
                                             match uu____28525 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28721 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28721
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28722 =
                                                   let g_sort_is =
                                                     let uu____28732 =
                                                       let uu____28733 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28733.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28732 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28738,uu____28739::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28799 ->
                                                         let uu____28800 =
                                                           let uu____28806 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28806)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28800 r
                                                      in
                                                   let uu____28812 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28847  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28847
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28868
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28868
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28812
                                                    in
                                                 (match uu____28722 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28895 =
                                                          let uu____28900 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28901 =
                                                            let uu____28902 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28902
                                                             in
                                                          (uu____28900,
                                                            uu____28901)
                                                           in
                                                        match uu____28895
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28930 =
                                                          let uu____28933 =
                                                            let uu____28936 =
                                                              let uu____28939
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28939
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28936
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28933
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28930
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28963 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28963
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
                                                        let uu____28974 =
                                                          let uu____28977 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28980 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28980)
                                                            uu____28977
                                                           in
                                                        solve_prob orig
                                                          uu____28974 [] wl6
                                                         in
                                                      let uu____28981 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28981))))))))))
           in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env  in
           let lift_c1 uu____29009 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____29011 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ
                      in
                   [uu____29011]
               | x -> x  in
             let c12 =
               let uu___3780_29014 = c11  in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3780_29014.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3780_29014.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3780_29014.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3780_29014.FStar_Syntax_Syntax.flags)
               }  in
             let uu____29015 =
               let uu____29020 =
                 FStar_All.pipe_right
                   (let uu___3783_29022 = c12  in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3783_29022.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3783_29022.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3783_29022.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3783_29022.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____29020
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____29015
               (fun uu____29036  ->
                  match uu____29036 with
                  | (c,g) ->
                      let uu____29043 =
                        let uu____29045 = FStar_TypeChecker_Env.is_trivial g
                           in
                        Prims.op_Negation uu____29045  in
                      if uu____29043
                      then
                        let uu____29048 =
                          let uu____29054 =
                            let uu____29056 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name
                               in
                            let uu____29058 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name
                               in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____29056 uu____29058
                             in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____29054)
                           in
                        FStar_Errors.raise_error uu____29048 r
                      else FStar_Syntax_Util.comp_to_comp_typ c)
              in
           let uu____29064 =
             FStar_TypeChecker_Env.is_layered_effect env
               c21.FStar_Syntax_Syntax.effect_name
              in
           if uu____29064
           then solve_layered_sub c11 edge c21
           else
             (let uu____29069 =
                ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                   (let uu____29072 =
                      FStar_Ident.lid_equals
                        c11.FStar_Syntax_Syntax.effect_name
                        c21.FStar_Syntax_Syntax.effect_name
                       in
                    Prims.op_Negation uu____29072))
                  &&
                  (FStar_TypeChecker_Env.is_reifiable_effect env
                     c21.FStar_Syntax_Syntax.effect_name)
                 in
              if uu____29069
              then
                let uu____29075 =
                  mklstr
                    (fun uu____29082  ->
                       let uu____29083 =
                         FStar_Ident.string_of_lid
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____29085 =
                         FStar_Ident.string_of_lid
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Cannot lift from %s to %s, it needs a lift\n"
                         uu____29083 uu____29085)
                   in
                giveup env uu____29075 orig
              else
                (let is_null_wp_2 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___29_29096  ->
                           match uu___29_29096 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | FStar_Syntax_Syntax.MLEFFECT  -> true
                           | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                           | uu____29101 -> false))
                    in
                 let uu____29103 =
                   match ((c11.FStar_Syntax_Syntax.effect_args),
                           (c21.FStar_Syntax_Syntax.effect_args))
                   with
                   | ((wp1,uu____29133)::uu____29134,(wp2,uu____29136)::uu____29137)
                       -> (wp1, wp2)
                   | uu____29210 ->
                       let uu____29235 =
                         let uu____29241 =
                           let uu____29243 =
                             FStar_Syntax_Print.lid_to_string
                               c11.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____29245 =
                             FStar_Syntax_Print.lid_to_string
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Got effects %s and %s, expected normalized effects"
                             uu____29243 uu____29245
                            in
                         (FStar_Errors.Fatal_ExpectNormalizedEffect,
                           uu____29241)
                          in
                       FStar_Errors.raise_error uu____29235
                         env.FStar_TypeChecker_Env.range
                    in
                 match uu____29103 with
                 | (wpc1,wpc2) ->
                     let uu____29255 = FStar_Util.physical_equality wpc1 wpc2
                        in
                     if uu____29255
                     then
                       let uu____29258 =
                         problem_using_guard orig
                           c11.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29258 wl
                     else
                       (let uu____29262 =
                          let uu____29269 =
                            FStar_TypeChecker_Env.effect_decl_opt env
                              c21.FStar_Syntax_Syntax.effect_name
                             in
                          FStar_Util.must uu____29269  in
                        match uu____29262 with
                        | (c2_decl,qualifiers) ->
                            let uu____29290 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____29290
                            then
                              let c1_repr =
                                let uu____29297 =
                                  let uu____29298 =
                                    let uu____29299 = lift_c1 ()  in
                                    FStar_Syntax_Syntax.mk_Comp uu____29299
                                     in
                                  let uu____29300 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____29298 uu____29300
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.4"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____29297
                                 in
                              let c2_repr =
                                let uu____29303 =
                                  let uu____29304 =
                                    FStar_Syntax_Syntax.mk_Comp c21  in
                                  let uu____29305 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____29304 uu____29305
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.5"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____29303
                                 in
                              let uu____29307 =
                                let uu____29312 =
                                  let uu____29314 =
                                    FStar_Syntax_Print.term_to_string c1_repr
                                     in
                                  let uu____29316 =
                                    FStar_Syntax_Print.term_to_string c2_repr
                                     in
                                  FStar_Util.format2
                                    "sub effect repr: %s <: %s" uu____29314
                                    uu____29316
                                   in
                                sub_prob wl c1_repr
                                  problem.FStar_TypeChecker_Common.relation
                                  c2_repr uu____29312
                                 in
                              (match uu____29307 with
                               | (prob,wl1) ->
                                   let wl2 =
                                     solve_prob orig
                                       (FStar_Pervasives_Native.Some
                                          (p_guard prob)) [] wl1
                                      in
                                   let uu____29322 = attempt [prob] wl2  in
                                   solve env uu____29322)
                            else
                              (let g =
                                 if env.FStar_TypeChecker_Env.lax
                                 then FStar_Syntax_Util.t_true
                                 else
                                   (let wpc1_2 =
                                      let uu____29342 = lift_c1 ()  in
                                      FStar_All.pipe_right uu____29342
                                        (fun ct  ->
                                           FStar_List.hd
                                             ct.FStar_Syntax_Syntax.effect_args)
                                       in
                                    if is_null_wp_2
                                    then
                                      ((let uu____29365 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other "Rel")
                                           in
                                        if uu____29365
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
                                          let uu____29375 =
                                            FStar_All.pipe_right c2_decl
                                              FStar_Syntax_Util.get_wp_trivial_combinator
                                             in
                                          match uu____29375 with
                                          | FStar_Pervasives_Native.None  ->
                                              failwith
                                                "Rel doesn't yet handle undefined trivial combinator in an effect"
                                          | FStar_Pervasives_Native.Some t ->
                                              t
                                           in
                                        let uu____29382 =
                                          let uu____29383 =
                                            let uu____29400 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____29403 =
                                              let uu____29414 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____29414; wpc1_2]  in
                                            (uu____29400, uu____29403)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____29383
                                           in
                                        FStar_Syntax_Syntax.mk uu____29382 r))
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
                                       let uu____29463 =
                                         let uu____29464 =
                                           let uu____29481 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____29484 =
                                             let uu____29495 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____29504 =
                                               let uu____29515 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____29515; wpc1_2]  in
                                             uu____29495 :: uu____29504  in
                                           (uu____29481, uu____29484)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____29464
                                          in
                                       FStar_Syntax_Syntax.mk uu____29463 r))
                                  in
                               (let uu____29569 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____29569
                                then
                                  let uu____29574 =
                                    let uu____29576 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Eager_unfolding;
                                        FStar_TypeChecker_Env.Primops;
                                        FStar_TypeChecker_Env.Simplify] env g
                                       in
                                    FStar_Syntax_Print.term_to_string
                                      uu____29576
                                     in
                                  FStar_Util.print1
                                    "WP guard (simplifed) is (%s)\n"
                                    uu____29574
                                else ());
                               (let uu____29580 =
                                  sub_prob wl
                                    c11.FStar_Syntax_Syntax.result_typ
                                    problem.FStar_TypeChecker_Common.relation
                                    c21.FStar_Syntax_Syntax.result_typ
                                    "result type"
                                   in
                                match uu____29580 with
                                | (base_prob,wl1) ->
                                    let wl2 =
                                      let uu____29589 =
                                        let uu____29592 =
                                          FStar_Syntax_Util.mk_conj
                                            (p_guard base_prob) g
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____29595  ->
                                             FStar_Pervasives_Native.Some
                                               uu____29595) uu____29592
                                         in
                                      solve_prob orig uu____29589 [] wl1  in
                                    let uu____29596 = attempt [base_prob] wl2
                                       in
                                    solve env uu____29596))))))
           in
        let uu____29597 = FStar_Util.physical_equality c1 c2  in
        if uu____29597
        then
          let uu____29600 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29600
        else
          ((let uu____29604 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29604
            then
              let uu____29609 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29611 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29609
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29611
            else ());
           (let uu____29616 =
              let uu____29625 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29628 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29625, uu____29628)  in
            match uu____29616 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29646),FStar_Syntax_Syntax.Total
                    (t2,uu____29648)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29665 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29665 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29667,FStar_Syntax_Syntax.Total uu____29668) ->
                     let uu____29685 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29685 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29689),FStar_Syntax_Syntax.Total
                    (t2,uu____29691)) ->
                     let uu____29708 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29708 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29711),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29713)) ->
                     let uu____29730 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29730 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29733),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29735)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29752 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29752 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29755),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29757)) ->
                     let uu____29774 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29774 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29777,FStar_Syntax_Syntax.Comp uu____29778) ->
                     let uu____29787 =
                       let uu___3908_29790 = problem  in
                       let uu____29793 =
                         let uu____29794 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29794
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3908_29790.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29793;
                         FStar_TypeChecker_Common.relation =
                           (uu___3908_29790.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3908_29790.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3908_29790.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3908_29790.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3908_29790.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3908_29790.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3908_29790.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3908_29790.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29787 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29795,FStar_Syntax_Syntax.Comp uu____29796) ->
                     let uu____29805 =
                       let uu___3908_29808 = problem  in
                       let uu____29811 =
                         let uu____29812 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29812
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3908_29808.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29811;
                         FStar_TypeChecker_Common.relation =
                           (uu___3908_29808.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3908_29808.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3908_29808.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3908_29808.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3908_29808.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3908_29808.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3908_29808.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3908_29808.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29805 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29813,FStar_Syntax_Syntax.GTotal uu____29814) ->
                     let uu____29823 =
                       let uu___3920_29826 = problem  in
                       let uu____29829 =
                         let uu____29830 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29830
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3920_29826.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3920_29826.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3920_29826.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29829;
                         FStar_TypeChecker_Common.element =
                           (uu___3920_29826.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3920_29826.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3920_29826.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3920_29826.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3920_29826.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3920_29826.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29823 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29831,FStar_Syntax_Syntax.Total uu____29832) ->
                     let uu____29841 =
                       let uu___3920_29844 = problem  in
                       let uu____29847 =
                         let uu____29848 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29848
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3920_29844.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3920_29844.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3920_29844.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29847;
                         FStar_TypeChecker_Common.element =
                           (uu___3920_29844.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3920_29844.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3920_29844.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3920_29844.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3920_29844.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3920_29844.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29841 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29849,FStar_Syntax_Syntax.Comp uu____29850) ->
                     let uu____29851 =
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
                     if uu____29851
                     then
                       let uu____29854 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29854 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29861 =
                            let uu____29866 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29866
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29875 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29876 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29875, uu____29876))
                             in
                          match uu____29861 with
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
                           (let uu____29884 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29884
                            then
                              let uu____29889 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29891 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29889 uu____29891
                            else ());
                           (let uu____29896 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29896 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29899 =
                                  mklstr
                                    (fun uu____29906  ->
                                       let uu____29907 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29909 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29907 uu____29909)
                                   in
                                giveup env uu____29899 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29920 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29920 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29970 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29970 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29995 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____30026  ->
                match uu____30026 with
                | (u1,u2) ->
                    let uu____30034 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____30036 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____30034 uu____30036))
         in
      FStar_All.pipe_right uu____29995 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____30073,[])) when
          let uu____30100 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____30100 -> "{}"
      | uu____30103 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____30130 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____30130
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry defs =
            let uu____30161 =
              FStar_List.map
                (fun uu____30175  ->
                   match uu____30175 with
                   | (msg,x) ->
                       let uu____30186 =
                         let uu____30188 = prob_to_string env x  in
                         Prims.op_Hat ": " uu____30188  in
                       Prims.op_Hat msg uu____30186) defs
               in
            FStar_All.pipe_right uu____30161 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30198 = carry g.FStar_TypeChecker_Common.deferred  in
          let uu____30200 = carry g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____30202 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30198 uu____30200 uu____30202 imps
  
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
                  let uu____30259 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30259
                  then
                    let uu____30267 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30269 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30267
                      (rel_to_string rel) uu____30269
                  else "TOP"  in
                let uu____30275 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30275 with
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
              let uu____30335 =
                let uu____30338 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____30341  ->
                     FStar_Pervasives_Native.Some uu____30341) uu____30338
                 in
              FStar_Syntax_Syntax.new_bv uu____30335 t1  in
            let uu____30342 =
              let uu____30347 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30347
               in
            match uu____30342 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____30419 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30419
         then
           let uu____30424 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30424
         else ());
        (let uu____30431 =
           FStar_Util.record_time (fun uu____30438  -> solve env probs)  in
         match uu____30431 with
         | (sol,ms) ->
             ((let uu____30452 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30452
               then
                 let uu____30457 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30457
               else ());
              (match sol with
               | Success (deferred,defer_to_tac,implicits) ->
                   let uu____30473 =
                     FStar_Util.record_time
                       (fun uu____30480  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30473 with
                    | ((),ms1) ->
                        ((let uu____30493 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30493
                          then
                            let uu____30498 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30498
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d,s) ->
                   ((let uu____30512 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30512
                     then
                       let uu____30519 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30519
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
          ((let uu____30547 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30547
            then
              let uu____30552 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30552
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30560 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30560
             then
               let uu____30565 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30565
             else ());
            (let f2 =
               let uu____30571 =
                 let uu____30572 = FStar_Syntax_Util.unmeta f1  in
                 uu____30572.FStar_Syntax_Syntax.n  in
               match uu____30571 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30576 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4039_30577 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4039_30577.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4039_30577.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4039_30577.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4039_30577.FStar_TypeChecker_Common.implicits)
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
            let uu____30629 =
              let uu____30630 =
                let uu____30631 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30632  ->
                       FStar_TypeChecker_Common.NonTrivial uu____30632)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30631;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30630  in
            FStar_All.pipe_left
              (fun uu____30639  -> FStar_Pervasives_Native.Some uu____30639)
              uu____30629
  
let with_guard_no_simp :
  'uuuuuu30649 .
    'uuuuuu30649 ->
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
            let uu____30698 =
              let uu____30699 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30700  ->
                     FStar_TypeChecker_Common.NonTrivial uu____30700)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30699;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30698
  
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
          (let uu____30733 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30733
           then
             let uu____30738 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30740 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30738
               uu____30740
           else ());
          (let uu____30745 =
             let uu____30750 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30750
              in
           match uu____30745 with
           | (prob,wl) ->
               let g =
                 let uu____30758 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30768  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30758  in
               ((let uu____30790 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30790
                 then
                   let uu____30795 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30795
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
        let uu____30816 = try_teq true env t1 t2  in
        match uu____30816 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30821 = FStar_TypeChecker_Env.get_range env  in
              let uu____30822 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30821 uu____30822);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30830 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30830
              then
                let uu____30835 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30837 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30839 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30835
                  uu____30837 uu____30839
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
        (let uu____30863 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30863
         then
           let uu____30868 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30870 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30868
             uu____30870
         else ());
        (let uu____30875 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30875 with
         | (prob,x,wl) ->
             let g =
               let uu____30890 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30901  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30890  in
             ((let uu____30923 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30923
               then
                 let uu____30928 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30928
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30936 =
                     let uu____30937 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30937 g1  in
                   FStar_Pervasives_Native.Some uu____30936)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30959 = FStar_TypeChecker_Env.get_range env  in
          let uu____30960 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30959 uu____30960
  
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
        (let uu____30989 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30989
         then
           let uu____30994 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30996 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30994 uu____30996
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____31007 =
           let uu____31014 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____31014 "sub_comp"
            in
         match uu____31007 with
         | (prob,wl) ->
             let wl1 =
               let uu___4112_31025 = wl  in
               {
                 attempting = (uu___4112_31025.attempting);
                 wl_deferred = (uu___4112_31025.wl_deferred);
                 wl_deferred_to_tac = (uu___4112_31025.wl_deferred_to_tac);
                 ctr = (uu___4112_31025.ctr);
                 defer_ok = (uu___4112_31025.defer_ok);
                 smt_ok = (uu___4112_31025.smt_ok);
                 umax_heuristic_ok = (uu___4112_31025.umax_heuristic_ok);
                 tcenv = (uu___4112_31025.tcenv);
                 wl_implicits = (uu___4112_31025.wl_implicits);
                 repr_subcomp_allowed = true
               }  in
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____31030 =
                 FStar_Util.record_time
                   (fun uu____31042  ->
                      let uu____31043 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____31054  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____31043)
                  in
               match uu____31030 with
               | (r,ms) ->
                   ((let uu____31086 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____31086
                     then
                       let uu____31091 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____31093 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____31095 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____31091 uu____31093
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____31095
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
      fun uu____31133  ->
        match uu____31133 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31176 =
                 let uu____31182 =
                   let uu____31184 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31186 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31184 uu____31186
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31182)  in
               let uu____31190 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31176 uu____31190)
               in
            let equiv v v' =
              let uu____31203 =
                let uu____31208 = FStar_Syntax_Subst.compress_univ v  in
                let uu____31209 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31208, uu____31209)  in
              match uu____31203 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31233 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____31264 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____31264 with
                      | FStar_Syntax_Syntax.U_unif uu____31271 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31302  ->
                                    match uu____31302 with
                                    | (u,v') ->
                                        let uu____31311 = equiv v v'  in
                                        if uu____31311
                                        then
                                          let uu____31316 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____31316 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____31337 -> []))
               in
            let uu____31342 =
              let wl =
                let uu___4155_31346 = empty_worklist env  in
                {
                  attempting = (uu___4155_31346.attempting);
                  wl_deferred = (uu___4155_31346.wl_deferred);
                  wl_deferred_to_tac = (uu___4155_31346.wl_deferred_to_tac);
                  ctr = (uu___4155_31346.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4155_31346.smt_ok);
                  umax_heuristic_ok = (uu___4155_31346.umax_heuristic_ok);
                  tcenv = (uu___4155_31346.tcenv);
                  wl_implicits = (uu___4155_31346.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4155_31346.repr_subcomp_allowed)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31365  ->
                      match uu____31365 with
                      | (lb,v) ->
                          let uu____31372 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____31372 with
                           | USolved wl1 -> ()
                           | uu____31375 -> fail lb v)))
               in
            let rec check_ineq uu____31386 =
              match uu____31386 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31398) -> true
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
                      uu____31426,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31428,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31441) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____31449,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____31458 -> false)
               in
            let uu____31464 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31481  ->
                      match uu____31481 with
                      | (u,v) ->
                          let uu____31489 = check_ineq (u, v)  in
                          if uu____31489
                          then true
                          else
                            ((let uu____31497 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31497
                              then
                                let uu____31502 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31504 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____31502
                                  uu____31504
                              else ());
                             false)))
               in
            if uu____31464
            then ()
            else
              ((let uu____31514 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31514
                then
                  ((let uu____31520 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31520);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31532 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31532))
                else ());
               (let uu____31545 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31545))
  
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
          let fail uu____31627 =
            match uu____31627 with
            | (d,s) ->
                let msg = explain env d s  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d)
             in
          let wl =
            let uu___4233_31654 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
            {
              attempting = (uu___4233_31654.attempting);
              wl_deferred = (uu___4233_31654.wl_deferred);
              wl_deferred_to_tac = (uu___4233_31654.wl_deferred_to_tac);
              ctr = (uu___4233_31654.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4233_31654.umax_heuristic_ok);
              tcenv = (uu___4233_31654.tcenv);
              wl_implicits = (uu___4233_31654.wl_implicits);
              repr_subcomp_allowed = (uu___4233_31654.repr_subcomp_allowed)
            }  in
          (let uu____31657 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____31657
           then
             let uu____31662 = FStar_Util.string_of_bool defer_ok  in
             let uu____31664 = wl_to_string wl  in
             let uu____31666 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits)
                in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31662 uu____31664 uu____31666
           else ());
          (let g1 =
             let uu____31672 = solve_and_commit env wl fail  in
             match uu____31672 with
             | FStar_Pervasives_Native.Some
                 (uu____31681::uu____31682,uu____31683,uu____31684) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred,defer_to_tac,imps) ->
                 let uu___4250_31718 = g  in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4250_31718.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4250_31718.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31724 ->
                 failwith "Impossible: should have raised a failure already"
              in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let uu___4255_31735 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4255_31735.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4255_31735.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4255_31735.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs = ([], []);
              FStar_TypeChecker_Common.implicits =
                (uu___4255_31735.FStar_TypeChecker_Common.implicits)
            }))
  
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
          (let uu____31831 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____31831
           then
             let uu____31836 = guard_to_string env g  in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31836
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g  in
           let ret_g =
             let uu___4272_31843 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4272_31843.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4272_31843.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4272_31843.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4272_31843.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31844 =
             let uu____31846 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31846  in
           if uu____31844
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____31858 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31859 =
                        let uu____31861 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31861
                         in
                      FStar_Errors.diag uu____31858 uu____31859)
                   else ();
                   (let vc1 =
                      let uu____31867 =
                        let uu____31871 =
                          let uu____31873 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31873  in
                        FStar_Pervasives_Native.Some uu____31871  in
                      FStar_Profiling.profile
                        (fun uu____31876  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31867 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug
                    then
                      (let uu____31880 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31881 =
                         let uu____31883 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31883
                          in
                       FStar_Errors.diag uu____31880 uu____31881)
                    else ();
                    (let uu____31889 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31889 "discharge_guard'" env vc1);
                    (let uu____31891 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31891 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____31900 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31901 =
                                 let uu____31903 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31903
                                  in
                               FStar_Errors.diag uu____31900 uu____31901)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____31913 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31914 =
                                 let uu____31916 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31916
                                  in
                               FStar_Errors.diag uu____31913 uu____31914)
                            else ();
                            (let vcs =
                               let uu____31930 = FStar_Options.use_tactics ()
                                  in
                               if uu____31930
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31952  ->
                                      (let uu____31954 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left
                                         (fun uu____31956  -> ()) uu____31954);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31999  ->
                                               match uu____31999 with
                                               | (env1,goal,opts) ->
                                                   let uu____32015 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____32015, opts)))))
                               else
                                 (let uu____32019 =
                                    let uu____32026 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____32026)  in
                                  [uu____32019])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____32059  ->
                                     match uu____32059 with
                                     | (env1,goal,opts) ->
                                         let uu____32069 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____32069 with
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
                                                 (let uu____32080 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____32081 =
                                                    let uu____32083 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____32085 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____32083 uu____32085
                                                     in
                                                  FStar_Errors.diag
                                                    uu____32080 uu____32081)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____32092 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____32093 =
                                                    let uu____32095 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____32095
                                                     in
                                                  FStar_Errors.diag
                                                    uu____32092 uu____32093)
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
      let uu____32113 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____32113 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____32122 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____32122
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____32136 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____32136 with
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
        let uu____32166 = try_teq false env t1 t2  in
        match uu____32166 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some g ->
            discharge_guard' FStar_Pervasives_Native.None env g false
  
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
            let uu____32210 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32210 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32217 ->
                     let uu____32218 =
                       let uu____32219 = FStar_Syntax_Subst.compress r  in
                       uu____32219.FStar_Syntax_Syntax.n  in
                     (match uu____32218 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32224) ->
                          unresolved ctx_u'
                      | uu____32241 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32265 = acc  in
            match uu____32265 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____32284 = hd  in
                     (match uu____32284 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____32295 = unresolved ctx_u  in
                             if uu____32295
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32306 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32306
                                     then
                                       let uu____32310 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32310
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32319 = teq_nosmt env1 t tm
                                          in
                                       match uu____32319 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4385_32329 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4385_32329.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4385_32329.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4385_32329.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4385_32329.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4385_32329.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4385_32329.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4385_32329.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4388_32331 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4388_32331.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4388_32331.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4388_32331.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl)))
                               | uu____32334 ->
                                   until_fixpoint ((hd :: out), changed) tl
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl
                               else
                                 (let env1 =
                                    let uu___4393_32346 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4393_32346.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4393_32346.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4393_32346.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4393_32346.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4393_32346.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4393_32346.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4393_32346.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4393_32346.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4393_32346.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4393_32346.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4393_32346.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4393_32346.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4393_32346.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4393_32346.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4393_32346.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4393_32346.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4393_32346.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4393_32346.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4393_32346.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4393_32346.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4393_32346.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4393_32346.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4393_32346.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4393_32346.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4393_32346.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4393_32346.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4393_32346.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4393_32346.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4393_32346.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4393_32346.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4393_32346.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4393_32346.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4393_32346.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4393_32346.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4393_32346.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4393_32346.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4393_32346.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4393_32346.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4393_32346.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4393_32346.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4393_32346.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4393_32346.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4393_32346.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4393_32346.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4393_32346.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___4393_32346.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4398_32351 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4398_32351.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4398_32351.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4398_32351.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4398_32351.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4398_32351.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4398_32351.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4398_32351.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4398_32351.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4398_32351.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4398_32351.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4398_32351.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4398_32351.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4398_32351.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4398_32351.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4398_32351.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4398_32351.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4398_32351.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4398_32351.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4398_32351.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4398_32351.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4398_32351.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4398_32351.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4398_32351.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4398_32351.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4398_32351.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4398_32351.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4398_32351.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4398_32351.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4398_32351.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4398_32351.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4398_32351.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4398_32351.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4398_32351.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4398_32351.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4398_32351.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4398_32351.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4398_32351.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4398_32351.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4398_32351.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4398_32351.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4398_32351.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4398_32351.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4398_32351.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4398_32351.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4398_32351.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4398_32351.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      }
                                    else env1  in
                                  (let uu____32356 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32356
                                   then
                                     let uu____32361 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32363 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32365 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32367 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32361 uu____32363 uu____32365
                                       reason uu____32367
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4404_32374  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32381 =
                                             let uu____32391 =
                                               let uu____32399 =
                                                 let uu____32401 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32403 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32405 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32401 uu____32403
                                                   uu____32405
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32399, r)
                                                in
                                             [uu____32391]  in
                                           FStar_Errors.add_errors
                                             uu____32381);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32424 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32435  ->
                                               let uu____32436 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32438 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32440 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32436 uu____32438
                                                 reason uu____32440)) env2 g1
                                         true
                                        in
                                     match uu____32424 with
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
          let uu___4416_32448 = g  in
          let uu____32449 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4416_32448.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4416_32448.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4416_32448.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4416_32448.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32449
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____32464 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32464
       then
         let uu____32469 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32469
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
      (let uu____32500 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32500
       then
         let uu____32505 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32505
       else ());
      (let g1 = solve_deferred_constraints env g  in
       let g2 =
         FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
           env g1
          in
       (let uu____32513 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ResolveImplicitsHook")
           in
        if uu____32513
        then
          let uu____32518 = guard_to_string env g2  in
          FStar_Util.print1
            "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
            uu____32518
        else ());
       (let g3 = resolve_implicits env g2  in
        match g3.FStar_TypeChecker_Common.implicits with
        | [] ->
            let uu____32524 = discharge_guard env g3  in
            FStar_All.pipe_left (fun uu____32525  -> ()) uu____32524
        | imp::uu____32527 ->
            let uu____32530 =
              let uu____32536 =
                let uu____32538 =
                  FStar_Syntax_Print.uvar_to_string
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                   in
                let uu____32540 =
                  FStar_TypeChecker_Normalize.term_to_string env
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                   in
                FStar_Util.format3
                  "Failed to resolve implicit argument %s of type %s introduced for %s"
                  uu____32538 uu____32540
                  imp.FStar_TypeChecker_Common.imp_reason
                 in
              (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32536)
               in
            FStar_Errors.raise_error uu____32530
              imp.FStar_TypeChecker_Common.imp_range))
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32560 = teq env t1 t2  in
        force_trivial_guard env uu____32560
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32579 = teq_nosmt env t1 t2  in
        match uu____32579 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4449_32598 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4449_32598.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4449_32598.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4449_32598.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4449_32598.FStar_TypeChecker_Common.implicits)
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
        (let uu____32634 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32634
         then
           let uu____32639 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32641 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32639
             uu____32641
         else ());
        (let uu____32646 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32646 with
         | (prob,x,wl) ->
             let g =
               let uu____32665 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32676  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32665  in
             ((let uu____32698 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____32698
               then
                 let uu____32703 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____32705 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____32707 =
                   let uu____32709 = FStar_Util.must g  in
                   guard_to_string env uu____32709  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32703 uu____32705 uu____32707
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
        let uu____32746 = check_subtyping env t1 t2  in
        match uu____32746 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32765 =
              let uu____32766 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32766 g  in
            FStar_Pervasives_Native.Some uu____32765
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32785 = check_subtyping env t1 t2  in
        match uu____32785 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32804 =
              let uu____32805 =
                let uu____32806 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32806]  in
              FStar_TypeChecker_Env.close_guard env uu____32805 g  in
            FStar_Pervasives_Native.Some uu____32804
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32844 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32844
         then
           let uu____32849 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32851 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32849
             uu____32851
         else ());
        (let uu____32856 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32856 with
         | (prob,x,wl) ->
             let g =
               let uu____32871 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32882  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32871  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32907 =
                      let uu____32908 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32908]  in
                    FStar_TypeChecker_Env.close_guard env uu____32907 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32949 = subtype_nosmt env t1 t2  in
        match uu____32949 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  