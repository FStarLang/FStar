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
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6667 with
             | (uu____6675,src',wl1) ->
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
                 | uu____6789 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6790 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6854  ->
                  fun uu____6855  ->
                    match (uu____6854, uu____6855) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6958 =
                          let uu____6960 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6960
                           in
                        if uu____6958
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6994 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6994
                           then
                             let uu____7011 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____7011)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6790 with | (isect,uu____7061) -> FStar_List.rev isect
  
let binders_eq :
  'uuuuuu7097 'uuuuuu7098 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu7097) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7098) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7156  ->
              fun uu____7157  ->
                match (uu____7156, uu____7157) with
                | ((a,uu____7176),(b,uu____7178)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'uuuuuu7194 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7194) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____7225  ->
           match uu____7225 with
           | (y,uu____7232) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'uuuuuu7242 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7242) Prims.list ->
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
                   let uu____7404 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____7404
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7437 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7489 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7533 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7554 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7562  ->
    match uu___19_7562 with
    | MisMatch (d1,d2) ->
        let uu____7574 =
          let uu____7576 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7578 =
            let uu____7580 =
              let uu____7582 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7582 ")"  in
            Prims.op_Hat ") (" uu____7580  in
          Prims.op_Hat uu____7576 uu____7578  in
        Prims.op_Hat "MisMatch (" uu____7574
    | HeadMatch u ->
        let uu____7589 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7589
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___20_7598  ->
    match uu___20_7598 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7615 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7630 =
            (let uu____7636 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                in
             let uu____7638 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             uu____7636 = uu____7638) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
             in
          if uu____7630 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7647 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7647 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7658 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7682 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7692 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7711 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7711
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7712 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7713 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7714 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7727 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7741 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7765) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7771,uu____7772) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7814) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7839;
             FStar_Syntax_Syntax.index = uu____7840;
             FStar_Syntax_Syntax.sort = t2;_},uu____7842)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7850 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7851 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7852 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7867 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7874 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7894 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7894
  
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
           { FStar_Syntax_Syntax.blob = uu____7913;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7914;
             FStar_Syntax_Syntax.ltyp = uu____7915;
             FStar_Syntax_Syntax.rng = uu____7916;_},uu____7917)
            ->
            let uu____7928 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7928 t21
        | (uu____7929,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7930;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7931;
             FStar_Syntax_Syntax.ltyp = uu____7932;
             FStar_Syntax_Syntax.rng = uu____7933;_})
            ->
            let uu____7944 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7944
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            let uu____7947 = FStar_Syntax_Syntax.bv_eq x y  in
            if uu____7947
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7958 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7958
            then FullMatch
            else
              (let uu____7963 =
                 let uu____7972 =
                   let uu____7975 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7975  in
                 let uu____7976 =
                   let uu____7979 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7979  in
                 (uu____7972, uu____7976)  in
               MisMatch uu____7963)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7985),FStar_Syntax_Syntax.Tm_uinst (g,uu____7987)) ->
            let uu____7996 = head_matches env f g  in
            FStar_All.pipe_right uu____7996 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7997) -> HeadMatch true
        | (uu____7999,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____8003 = FStar_Const.eq_const c d  in
            if uu____8003
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____8013),FStar_Syntax_Syntax.Tm_uvar (uv',uu____8015)) ->
            let uu____8048 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____8048
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____8058),FStar_Syntax_Syntax.Tm_refine (y,uu____8060)) ->
            let uu____8069 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8069 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____8071),uu____8072) ->
            let uu____8077 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____8077 head_match
        | (uu____8078,FStar_Syntax_Syntax.Tm_refine (x,uu____8080)) ->
            let uu____8085 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8085 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8086,FStar_Syntax_Syntax.Tm_type
           uu____8087) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____8089,FStar_Syntax_Syntax.Tm_arrow uu____8090) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____8121),FStar_Syntax_Syntax.Tm_app (head',uu____8123))
            ->
            let uu____8172 = head_matches env head head'  in
            FStar_All.pipe_right uu____8172 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____8174),uu____8175) ->
            let uu____8200 = head_matches env head t21  in
            FStar_All.pipe_right uu____8200 head_match
        | (uu____8201,FStar_Syntax_Syntax.Tm_app (head,uu____8203)) ->
            let uu____8228 = head_matches env t11 head  in
            FStar_All.pipe_right uu____8228 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8229,FStar_Syntax_Syntax.Tm_let
           uu____8230) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____8258,FStar_Syntax_Syntax.Tm_match uu____8259) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8305,FStar_Syntax_Syntax.Tm_abs
           uu____8306) -> HeadMatch true
        | uu____8344 ->
            let uu____8349 =
              let uu____8358 = delta_depth_of_term env t11  in
              let uu____8361 = delta_depth_of_term env t21  in
              (uu____8358, uu____8361)  in
            MisMatch uu____8349
  
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
              let uu____8430 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8430  in
            (let uu____8432 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8432
             then
               let uu____8437 = FStar_Syntax_Print.term_to_string t  in
               let uu____8439 = FStar_Syntax_Print.term_to_string head  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8437 uu____8439
             else ());
            (let uu____8444 =
               let uu____8445 = FStar_Syntax_Util.un_uinst head  in
               uu____8445.FStar_Syntax_Syntax.n  in
             match uu____8444 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8451 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8451 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8465 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8465
                        then
                          let uu____8470 =
                            FStar_Syntax_Print.term_to_string head  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8470
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8475 ->
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
                      let uu____8493 =
                        let uu____8495 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8495 = FStar_Syntax_Util.Equal  in
                      if uu____8493
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8502 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8502
                          then
                            let uu____8507 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8509 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8507
                              uu____8509
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8514 -> FStar_Pervasives_Native.None)
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
            (let uu____8666 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8666
             then
               let uu____8671 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8673 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8675 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8671
                 uu____8673 uu____8675
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8703 =
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
               match uu____8703 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8751 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8751 with
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
                  uu____8789),uu____8790)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8811 =
                      let uu____8820 = maybe_inline t11  in
                      let uu____8823 = maybe_inline t21  in
                      (uu____8820, uu____8823)  in
                    match uu____8811 with
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
                 (uu____8866,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8867))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8888 =
                      let uu____8897 = maybe_inline t11  in
                      let uu____8900 = maybe_inline t21  in
                      (uu____8897, uu____8900)  in
                    match uu____8888 with
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
             | MisMatch uu____8955 -> fail n_delta r t11 t21
             | uu____8964 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8979 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8979
           then
             let uu____8984 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8986 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8988 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8996 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____9013 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____9013
                    (fun uu____9048  ->
                       match uu____9048 with
                       | (t11,t21) ->
                           let uu____9056 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____9058 =
                             let uu____9060 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____9060  in
                           Prims.op_Hat uu____9056 uu____9058))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8984 uu____8986 uu____8988 uu____8996
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____9077 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____9077 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_9092  ->
    match uu___21_9092 with
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
      let uu___1259_9141 = p  in
      let uu____9144 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____9145 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1259_9141.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9144;
        FStar_TypeChecker_Common.relation =
          (uu___1259_9141.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9145;
        FStar_TypeChecker_Common.element =
          (uu___1259_9141.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1259_9141.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1259_9141.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1259_9141.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1259_9141.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1259_9141.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9160 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____9160
            (fun uu____9165  -> FStar_TypeChecker_Common.TProb uu____9165)
      | FStar_TypeChecker_Common.CProb uu____9166 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____9189 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____9189 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9197 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9197 with
           | (lh,lhs_args) ->
               let uu____9244 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9244 with
                | (rh,rhs_args) ->
                    let uu____9291 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9304,FStar_Syntax_Syntax.Tm_uvar uu____9305)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9394 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9421,uu____9422)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9437,FStar_Syntax_Syntax.Tm_uvar uu____9438)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9453,FStar_Syntax_Syntax.Tm_arrow uu____9454)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9484 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_9484.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_9484.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_9484.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_9484.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_9484.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_9484.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_9484.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_9484.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_9484.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9487,FStar_Syntax_Syntax.Tm_type uu____9488)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9504 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_9504.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_9504.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_9504.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_9504.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_9504.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_9504.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_9504.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_9504.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_9504.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9507,FStar_Syntax_Syntax.Tm_uvar uu____9508)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1310_9524 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1310_9524.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1310_9524.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1310_9524.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1310_9524.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1310_9524.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1310_9524.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1310_9524.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1310_9524.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1310_9524.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9527,FStar_Syntax_Syntax.Tm_uvar uu____9528)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9543,uu____9544)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9559,FStar_Syntax_Syntax.Tm_uvar uu____9560)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9575,uu____9576) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9291 with
                     | (rank,tp1) ->
                         let uu____9589 =
                           FStar_All.pipe_right
                             (let uu___1330_9593 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1330_9593.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1330_9593.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1330_9593.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1330_9593.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1330_9593.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1330_9593.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1330_9593.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1330_9593.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1330_9593.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9596  ->
                                FStar_TypeChecker_Common.TProb uu____9596)
                            in
                         (rank, uu____9589))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9600 =
            FStar_All.pipe_right
              (let uu___1334_9604 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1334_9604.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1334_9604.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1334_9604.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1334_9604.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1334_9604.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1334_9604.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1334_9604.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1334_9604.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1334_9604.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9607  -> FStar_TypeChecker_Common.CProb uu____9607)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9600)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9667 probs =
      match uu____9667 with
      | (min_rank,min,out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9748 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9769 = rank wl.tcenv hd  in
               (match uu____9769 with
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
                      (let uu____9830 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9835 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9835)
                          in
                       if uu____9830
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
          let uu____9908 = FStar_Syntax_Util.head_and_args t  in
          match uu____9908 with
          | (hd,uu____9927) ->
              let uu____9952 =
                let uu____9953 = FStar_Syntax_Subst.compress hd  in
                uu____9953.FStar_Syntax_Syntax.n  in
              (match uu____9952 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9958) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9993  ->
                           match uu____9993 with
                           | (y,uu____10002) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____10025  ->
                                       match uu____10025 with
                                       | (x,uu____10034) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____10039 -> false)
           in
        let uu____10041 = rank tcenv p  in
        match uu____10041 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____10050 -> true
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
    match projectee with | UDeferred _0 -> true | uu____10131 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____10150 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____10169 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____10186 = FStar_Thunk.mkv s  in UFailed uu____10186 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____10201 = mklstr s  in UFailed uu____10201 
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
                        let uu____10252 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____10252 with
                        | (k,uu____10260) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10275 -> false)))
            | uu____10277 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10329 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  FStar_Syntax_Util.eq_univs uv1 uv2))
                           in
                        if uu____10329 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____10353 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  -> FStar_Syntax_Util.eq_univs u u'))
                      in
                   Prims.op_Negation uu____10353)
               in
            let uu____10360 = filter u12  in
            let uu____10363 = filter u22  in (uu____10360, uu____10363)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10398 = filter_out_common_univs us1 us2  in
                   (match uu____10398 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10458 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10458 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10461 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10478  ->
                               let uu____10479 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10481 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10479 uu____10481))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10507 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10507 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10533 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10533 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10536 ->
                   ufailed_thunk
                     (fun uu____10547  ->
                        let uu____10548 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10550 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10548 uu____10550 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10553,uu____10554) ->
              let uu____10556 =
                let uu____10558 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10560 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10558 uu____10560
                 in
              failwith uu____10556
          | (FStar_Syntax_Syntax.U_unknown ,uu____10563) ->
              let uu____10564 =
                let uu____10566 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10568 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10566 uu____10568
                 in
              failwith uu____10564
          | (uu____10571,FStar_Syntax_Syntax.U_bvar uu____10572) ->
              let uu____10574 =
                let uu____10576 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10578 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10576 uu____10578
                 in
              failwith uu____10574
          | (uu____10581,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10582 =
                let uu____10584 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10586 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10584 uu____10586
                 in
              failwith uu____10582
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              let uu____10591 =
                let uu____10593 = FStar_Ident.string_of_id x  in
                let uu____10595 = FStar_Ident.string_of_id y  in
                uu____10593 = uu____10595  in
              if uu____10591
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10626 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10626
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10645 = occurs_univ v1 u3  in
              if uu____10645
              then
                let uu____10648 =
                  let uu____10650 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10652 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10650 uu____10652
                   in
                try_umax_components u11 u21 uu____10648
              else
                (let uu____10657 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10657)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10671 = occurs_univ v1 u3  in
              if uu____10671
              then
                let uu____10674 =
                  let uu____10676 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10678 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10676 uu____10678
                   in
                try_umax_components u11 u21 uu____10674
              else
                (let uu____10683 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10683)
          | (FStar_Syntax_Syntax.U_max uu____10684,uu____10685) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10693 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10693
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10699,FStar_Syntax_Syntax.U_max uu____10700) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10708 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10708
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10714,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10716,FStar_Syntax_Syntax.U_name uu____10717) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10719) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10721) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10723,FStar_Syntax_Syntax.U_succ uu____10724) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10726,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10833 = bc1  in
      match uu____10833 with
      | (bs1,mk_cod1) ->
          let uu____10877 = bc2  in
          (match uu____10877 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10988 = aux xs ys  in
                     (match uu____10988 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____11071 =
                       let uu____11078 = mk_cod1 xs  in ([], uu____11078)  in
                     let uu____11081 =
                       let uu____11088 = mk_cod2 ys  in ([], uu____11088)  in
                     (uu____11071, uu____11081)
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
                  let uu____11157 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____11157 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____11160 =
                    let uu____11161 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____11161 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____11160
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____11166 = has_type_guard t1 t2  in (uu____11166, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____11167 = has_type_guard t2 t1  in (uu____11167, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_11174  ->
    match uu___22_11174 with
    | Flex (uu____11176,uu____11177,[]) -> true
    | uu____11187 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____11201 = f  in
      match uu____11201 with
      | Flex (uu____11203,u,uu____11205) ->
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
      let uu____11229 = f  in
      match uu____11229 with
      | Flex
          (uu____11236,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____11237;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11238;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____11241;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____11242;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____11243;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____11244;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11310  ->
                 match uu____11310 with
                 | (y,uu____11319) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11473 =
                  let uu____11488 =
                    let uu____11491 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11491  in
                  ((FStar_List.rev pat_binders), uu____11488)  in
                FStar_Pervasives_Native.Some uu____11473
            | (uu____11524,[]) ->
                let uu____11555 =
                  let uu____11570 =
                    let uu____11573 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11573  in
                  ((FStar_List.rev pat_binders), uu____11570)  in
                FStar_Pervasives_Native.Some uu____11555
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11664 =
                  let uu____11665 = FStar_Syntax_Subst.compress a  in
                  uu____11665.FStar_Syntax_Syntax.n  in
                (match uu____11664 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11685 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11685
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1671_11715 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1671_11715.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1671_11715.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11719 =
                            let uu____11720 =
                              let uu____11727 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11727)  in
                            FStar_Syntax_Syntax.NT uu____11720  in
                          [uu____11719]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1677_11743 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1677_11743.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1677_11743.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11744 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11784 =
                  let uu____11791 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11791  in
                (match uu____11784 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11850 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11875 ->
               let uu____11876 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11876 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____12208 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____12208
       then
         let uu____12213 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12213
       else ());
      (let uu____12219 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____12219
       then
         let uu____12224 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12224
       else ());
      (let uu____12229 = next_prob probs  in
       match uu____12229 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1704_12256 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1704_12256.wl_deferred);
               wl_deferred_to_tac = (uu___1704_12256.wl_deferred_to_tac);
               ctr = (uu___1704_12256.ctr);
               defer_ok = (uu___1704_12256.defer_ok);
               smt_ok = (uu___1704_12256.smt_ok);
               umax_heuristic_ok = (uu___1704_12256.umax_heuristic_ok);
               tcenv = (uu___1704_12256.tcenv);
               wl_implicits = (uu___1704_12256.wl_implicits);
               repr_subcomp_allowed = (uu___1704_12256.repr_subcomp_allowed)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12265 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____12265
                 then
                   let uu____12268 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____12268
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
                           (let uu___1716_12280 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1716_12280.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1716_12280.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1716_12280.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1716_12280.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1716_12280.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1716_12280.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1716_12280.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1716_12280.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1716_12280.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12300 =
                  let uu____12307 = as_deferred probs.wl_deferred_to_tac  in
                  ([], uu____12307, (probs.wl_implicits))  in
                Success uu____12300
            | uu____12313 ->
                let uu____12323 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12388  ->
                          match uu____12388 with
                          | (c,uu____12398,uu____12399) -> c < probs.ctr))
                   in
                (match uu____12323 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12447 =
                            let uu____12454 = as_deferred probs.wl_deferred
                               in
                            let uu____12455 =
                              as_deferred probs.wl_deferred_to_tac  in
                            (uu____12454, uu____12455, (probs.wl_implicits))
                             in
                          Success uu____12447
                      | uu____12456 ->
                          let uu____12466 =
                            let uu___1730_12467 = probs  in
                            let uu____12468 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12489  ->
                                      match uu____12489 with
                                      | (uu____12497,uu____12498,y) -> y))
                               in
                            {
                              attempting = uu____12468;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1730_12467.wl_deferred_to_tac);
                              ctr = (uu___1730_12467.ctr);
                              defer_ok = (uu___1730_12467.defer_ok);
                              smt_ok = (uu___1730_12467.smt_ok);
                              umax_heuristic_ok =
                                (uu___1730_12467.umax_heuristic_ok);
                              tcenv = (uu___1730_12467.tcenv);
                              wl_implicits = (uu___1730_12467.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1730_12467.repr_subcomp_allowed)
                            }  in
                          solve env uu____12466))))

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
            let uu____12507 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12507 with
            | USolved wl1 ->
                let uu____12509 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12509
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12512 = defer_lit "" orig wl1  in
                solve env uu____12512

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
                  let uu____12563 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12563 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12566 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12579;
                  FStar_Syntax_Syntax.vars = uu____12580;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12583;
                  FStar_Syntax_Syntax.vars = uu____12584;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12597,uu____12598) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12606,FStar_Syntax_Syntax.Tm_uinst uu____12607) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12615 -> USolved wl

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
            ((let uu____12626 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12626
              then
                let uu____12631 = prob_to_string env orig  in
                let uu____12633 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12631 uu____12633
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
            let uu___1812_12648 = wl1  in
            let uu____12649 =
              let uu____12659 =
                let uu____12667 = FStar_Thunk.mkv reason  in
                ((wl1.ctr), uu____12667, orig)  in
              uu____12659 :: (wl1.wl_deferred_to_tac)  in
            {
              attempting = (uu___1812_12648.attempting);
              wl_deferred = (uu___1812_12648.wl_deferred);
              wl_deferred_to_tac = uu____12649;
              ctr = (uu___1812_12648.ctr);
              defer_ok = (uu___1812_12648.defer_ok);
              smt_ok = (uu___1812_12648.smt_ok);
              umax_heuristic_ok = (uu___1812_12648.umax_heuristic_ok);
              tcenv = (uu___1812_12648.tcenv);
              wl_implicits = (uu___1812_12648.wl_implicits);
              repr_subcomp_allowed = (uu___1812_12648.repr_subcomp_allowed)
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
                let uu____12696 = FStar_Syntax_Util.head_and_args t  in
                match uu____12696 with
                | (head,uu____12720) ->
                    let uu____12745 =
                      let uu____12746 = FStar_Syntax_Subst.compress head  in
                      uu____12746.FStar_Syntax_Syntax.n  in
                    (match uu____12745 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12756) ->
                         let uu____12773 =
                           FStar_TypeChecker_DeferredImplicits.should_defer_uvar_to_user_tac
                             wl.tcenv uv
                            in
                         (uu____12773,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12777 -> (false, ""))
                 in
              let uu____12782 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs  in
              (match uu____12782 with
               | (l1,r1) ->
                   let uu____12795 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs  in
                   (match uu____12795 with
                    | (l2,r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12812 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl
                              in
                           solve env uu____12812)))
          | uu____12813 ->
              let uu____12814 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl  in
              solve env uu____12814

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
               let uu____12900 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12900 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12955 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12955
                then
                  let uu____12960 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12962 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12960 uu____12962
                else ());
               (let uu____12967 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12967 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____13013 = eq_prob t1 t2 wl2  in
                         (match uu____13013 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____13034 ->
                         let uu____13043 = eq_prob t1 t2 wl2  in
                         (match uu____13043 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13093 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13108 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13109 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13108, uu____13109)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13114 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13115 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13114, uu____13115)
                            in
                         (match uu____13093 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13146 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13146 with
                                | (t1_hd,t1_args) ->
                                    let uu____13191 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13191 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13257 =
                                              let uu____13264 =
                                                let uu____13275 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____13275 :: t1_args  in
                                              let uu____13292 =
                                                let uu____13301 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____13301 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____13350  ->
                                                   fun uu____13351  ->
                                                     fun uu____13352  ->
                                                       match (uu____13350,
                                                               uu____13351,
                                                               uu____13352)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____13402),
                                                          (a2,uu____13404))
                                                           ->
                                                           let uu____13441 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13441
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13264
                                                uu____13292
                                               in
                                            match uu____13257 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1915_13467 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1915_13467.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1915_13467.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1915_13467.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1915_13467.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1915_13467.repr_subcomp_allowed)
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13478 =
                                                  solve env1 wl'  in
                                                (match uu____13478 with
                                                 | Success
                                                     (uu____13481,defer_to_tac,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13485 =
                                                         extend_wl wl4
                                                           defer_to_tac imps
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13485))
                                                 | Failed uu____13486 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13518 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13518 with
                                | (t1_base,p1_opt) ->
                                    let uu____13554 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13554 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13653 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13653
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
                                               let uu____13706 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13706
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
                                               let uu____13738 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13738
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
                                               let uu____13770 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13770
                                           | uu____13773 -> t_base  in
                                         let uu____13790 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13790 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13804 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13804, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13811 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13811 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13847 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13847 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13883 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13883
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
                              let uu____13907 = combine t11 t21 wl2  in
                              (match uu____13907 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13940 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13940
                                     then
                                       let uu____13945 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13945
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13987 ts1 =
               match uu____13987 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____14050 = pairwise out t wl2  in
                        (match uu____14050 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14086 =
               let uu____14097 = FStar_List.hd ts  in (uu____14097, [], wl1)
                in
             let uu____14106 = FStar_List.tl ts  in
             aux uu____14086 uu____14106  in
           let uu____14113 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14113 with
           | (this_flex,this_rigid) ->
               let uu____14139 =
                 let uu____14140 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14140.FStar_Syntax_Syntax.n  in
               (match uu____14139 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14165 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14165
                    then
                      let uu____14168 = destruct_flex_t this_flex wl  in
                      (match uu____14168 with
                       | (flex,wl1) ->
                           let uu____14175 = quasi_pattern env flex  in
                           (match uu____14175 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____14194 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14194
                                  then
                                    let uu____14199 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14199
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14206 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2025_14209 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2025_14209.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2025_14209.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2025_14209.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2025_14209.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2025_14209.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2025_14209.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2025_14209.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2025_14209.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2025_14209.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14206)
                | uu____14210 ->
                    ((let uu____14212 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14212
                      then
                        let uu____14217 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14217
                      else ());
                     (let uu____14222 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14222 with
                      | (u,_args) ->
                          let uu____14265 =
                            let uu____14266 = FStar_Syntax_Subst.compress u
                               in
                            uu____14266.FStar_Syntax_Syntax.n  in
                          (match uu____14265 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____14294 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____14294 with
                                 | (u',uu____14313) ->
                                     let uu____14338 =
                                       let uu____14339 = whnf env u'  in
                                       uu____14339.FStar_Syntax_Syntax.n  in
                                     (match uu____14338 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14361 -> false)
                                  in
                               let uu____14363 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_14386  ->
                                         match uu___23_14386 with
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
                                              | uu____14400 -> false)
                                         | uu____14404 -> false))
                                  in
                               (match uu____14363 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14419 = whnf env this_rigid
                                         in
                                      let uu____14420 =
                                        FStar_List.collect
                                          (fun uu___24_14426  ->
                                             match uu___24_14426 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14432 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14432]
                                             | uu____14436 -> [])
                                          bounds_probs
                                         in
                                      uu____14419 :: uu____14420  in
                                    let uu____14437 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14437 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14470 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14485 =
                                               let uu____14486 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14486.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14485 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14498 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14498)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14509 -> bound  in
                                           let uu____14510 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14510)  in
                                         (match uu____14470 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14545 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14545
                                                then
                                                  let wl'1 =
                                                    let uu___2085_14551 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2085_14551.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2085_14551.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2085_14551.ctr);
                                                      defer_ok =
                                                        (uu___2085_14551.defer_ok);
                                                      smt_ok =
                                                        (uu___2085_14551.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2085_14551.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2085_14551.tcenv);
                                                      wl_implicits =
                                                        (uu___2085_14551.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2085_14551.repr_subcomp_allowed)
                                                    }  in
                                                  let uu____14552 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14552
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14558 =
                                                  solve_t env eq_prob
                                                    (let uu___2090_14560 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2090_14560.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2090_14560.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2090_14560.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2090_14560.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2090_14560.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2090_14560.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2090_14560.repr_subcomp_allowed)
                                                     })
                                                   in
                                                match uu____14558 with
                                                | Success
                                                    (uu____14562,defer_to_tac,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2097_14566 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2097_14566.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2097_14566.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2097_14566.ctr);
                                                        defer_ok =
                                                          (uu___2097_14566.defer_ok);
                                                        smt_ok =
                                                          (uu___2097_14566.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2097_14566.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2097_14566.tcenv);
                                                        wl_implicits =
                                                          (uu___2097_14566.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2097_14566.repr_subcomp_allowed)
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
                                                    let uu____14583 =
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
                                                    ((let uu____14595 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14595
                                                      then
                                                        let uu____14600 =
                                                          let uu____14602 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14602
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14600
                                                      else ());
                                                     (let uu____14615 =
                                                        let uu____14630 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14630)
                                                         in
                                                      match uu____14615 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14652))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14678 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14678
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
                                                                  let uu____14698
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14698))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14723 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14723
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
                                                                    let uu____14743
                                                                    =
                                                                    let uu____14748
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14748
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14743
                                                                    [] wl2
                                                                     in
                                                                  let uu____14754
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14754))))
                                                      | uu____14755 ->
                                                          let uu____14770 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14770 p)))))))
                           | uu____14777 when flip ->
                               let uu____14778 =
                                 let uu____14780 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14782 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14780 uu____14782
                                  in
                               failwith uu____14778
                           | uu____14785 ->
                               let uu____14786 =
                                 let uu____14788 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14790 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14788 uu____14790
                                  in
                               failwith uu____14786)))))

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
                      (fun uu____14826  ->
                         match uu____14826 with
                         | (x,i) ->
                             let uu____14845 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14845, i)) bs_lhs
                     in
                  let uu____14848 = lhs  in
                  match uu____14848 with
                  | Flex (uu____14849,u_lhs,uu____14851) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14948 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14958 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14958, univ)
                             in
                          match uu____14948 with
                          | (k,univ) ->
                              let uu____14965 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14965 with
                               | (uu____14982,u,wl3) ->
                                   let uu____14985 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14985, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____15011 =
                              let uu____15024 =
                                let uu____15035 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____15035 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15086  ->
                                   fun uu____15087  ->
                                     match (uu____15086, uu____15087) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15188 =
                                           let uu____15195 =
                                             let uu____15198 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15198
                                              in
                                           copy_uvar u_lhs [] uu____15195 wl2
                                            in
                                         (match uu____15188 with
                                          | (uu____15227,t_a,wl3) ->
                                              let uu____15230 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____15230 with
                                               | (uu____15249,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____15024
                                ([], wl1)
                               in
                            (match uu____15011 with
                             | (out_args,wl2) ->
                                 let nodec flags =
                                   FStar_List.filter
                                     (fun uu___25_15318  ->
                                        match uu___25_15318 with
                                        | FStar_Syntax_Syntax.DECREASES
                                            uu____15320 -> false
                                        | uu____15324 -> true) flags
                                    in
                                 let ct' =
                                   let uu___2216_15327 = ct  in
                                   let uu____15328 =
                                     let uu____15331 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____15331
                                      in
                                   let uu____15346 = FStar_List.tl out_args
                                      in
                                   let uu____15363 =
                                     nodec ct.FStar_Syntax_Syntax.flags  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2216_15327.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2216_15327.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15328;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15346;
                                     FStar_Syntax_Syntax.flags = uu____15363
                                   }  in
                                 ((let uu___2219_15367 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2219_15367.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2219_15367.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____15370 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____15370 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15408 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____15408 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15419 =
                                          let uu____15424 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15424)  in
                                        TERM uu____15419  in
                                      let uu____15425 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15425 with
                                       | (sub_prob,wl3) ->
                                           let uu____15439 =
                                             let uu____15440 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15440
                                              in
                                           solve env uu____15439))
                             | (x,imp)::formals2 ->
                                 let uu____15462 =
                                   let uu____15469 =
                                     let uu____15472 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15472
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15469 wl1
                                    in
                                 (match uu____15462 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15493 =
                                          let uu____15496 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15496
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15493 u_x
                                         in
                                      let uu____15497 =
                                        let uu____15500 =
                                          let uu____15503 =
                                            let uu____15504 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15504, imp)  in
                                          [uu____15503]  in
                                        FStar_List.append bs_terms
                                          uu____15500
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15497 formals2 wl2)
                              in
                           let uu____15531 = occurs_check u_lhs arrow  in
                           (match uu____15531 with
                            | (uu____15544,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15560 =
                                    mklstr
                                      (fun uu____15565  ->
                                         let uu____15566 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15566)
                                     in
                                  giveup_or_defer env orig wl uu____15560
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
              (let uu____15599 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15599
               then
                 let uu____15604 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15607 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15604 (rel_to_string (p_rel orig)) uu____15607
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15738 = rhs wl1 scope env1 subst  in
                     (match uu____15738 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15761 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15761
                            then
                              let uu____15766 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15766
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15844 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15844 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2289_15846 = hd1  in
                       let uu____15847 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2289_15846.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2289_15846.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15847
                       }  in
                     let hd21 =
                       let uu___2292_15851 = hd2  in
                       let uu____15852 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2292_15851.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2292_15851.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15852
                       }  in
                     let uu____15855 =
                       let uu____15860 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15860
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15855 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15883 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15883
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15890 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15890 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15962 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15962
                                  in
                               ((let uu____15980 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15980
                                 then
                                   let uu____15985 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15987 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15985
                                     uu____15987
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____16022 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____16058 = aux wl [] env [] bs1 bs2  in
               match uu____16058 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16117 = attempt sub_probs wl2  in
                   solve env1 uu____16117)

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
            let uu___2330_16137 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2330_16137.wl_deferred_to_tac);
              ctr = (uu___2330_16137.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2330_16137.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2330_16137.repr_subcomp_allowed)
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16149 = try_solve env wl'  in
          match uu____16149 with
          | Success (uu____16150,defer_to_tac,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps  in solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16163 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16163 wl)

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
            let uu____16169 = should_defer_flex_to_user_tac wl lhs  in
            if uu____16169
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16182 =
                   FStar_List.map FStar_Pervasives_Native.fst bs  in
                 FStar_Util.as_set uu____16182 FStar_Syntax_Syntax.order_bv
                  in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16216 = lhs1  in
                 match uu____16216 with
                 | Flex (uu____16219,ctx_u,uu____16221) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16229 ->
                           let uu____16230 = sn_binders env1 bs  in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16230 rhs1
                        in
                     [TERM (ctx_u, sol)]
                  in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16279 = quasi_pattern env1 lhs1  in
                 match uu____16279 with
                 | FStar_Pervasives_Native.None  ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs,uu____16313) ->
                     let uu____16318 = lhs1  in
                     (match uu____16318 with
                      | Flex (t_lhs,ctx_u,args) ->
                          let uu____16333 = occurs_check ctx_u rhs1  in
                          (match uu____16333 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16384 =
                                   let uu____16392 =
                                     let uu____16394 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16394
                                      in
                                   FStar_Util.Inl uu____16392  in
                                 (uu____16384, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs)
                                     in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1
                                     in
                                  let uu____16422 =
                                    let uu____16424 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs
                                       in
                                    Prims.op_Negation uu____16424  in
                                  if uu____16422
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16451 =
                                       let uu____16459 =
                                         mk_solution env1 lhs1 bs rhs1  in
                                       FStar_Util.Inr uu____16459  in
                                     let uu____16465 =
                                       restrict_all_uvars ctx_u uvars wl1  in
                                     (uu____16451, uu____16465)))))
                  in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16509 = FStar_Syntax_Util.head_and_args rhs1  in
                 match uu____16509 with
                 | (rhs_hd,args) ->
                     let uu____16552 = FStar_Util.prefix args  in
                     (match uu____16552 with
                      | (args_rhs,last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              rhs1.FStar_Syntax_Syntax.pos
                             in
                          let uu____16622 = lhs1  in
                          (match uu____16622 with
                           | Flex (t_lhs,u_lhs,_lhs_args) ->
                               let uu____16626 =
                                 let uu____16637 =
                                   let uu____16644 =
                                     let uu____16647 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16647
                                      in
                                   copy_uvar u_lhs [] uu____16644 wl1  in
                                 match uu____16637 with
                                 | (uu____16674,t_last_arg,wl2) ->
                                     let uu____16677 =
                                       let uu____16684 =
                                         let uu____16685 =
                                           let uu____16694 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg
                                              in
                                           [uu____16694]  in
                                         FStar_List.append bs_lhs uu____16685
                                          in
                                       copy_uvar u_lhs uu____16684 t_res_lhs
                                         wl2
                                        in
                                     (match uu____16677 with
                                      | (uu____16729,lhs',wl3) ->
                                          let uu____16732 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3
                                             in
                                          (match uu____16732 with
                                           | (uu____16749,lhs'_last_arg,wl4)
                                               -> (lhs', lhs'_last_arg, wl4)))
                                  in
                               (match uu____16626 with
                                | (lhs',lhs'_last_arg,wl2) ->
                                    let sol =
                                      let uu____16770 =
                                        let uu____16771 =
                                          let uu____16776 =
                                            let uu____16777 =
                                              let uu____16780 =
                                                let uu____16781 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    lhs'_last_arg
                                                   in
                                                [uu____16781]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                lhs' uu____16780
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16777
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16776)  in
                                        TERM uu____16771  in
                                      [uu____16770]  in
                                    let uu____16806 =
                                      let uu____16813 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs"
                                         in
                                      match uu____16813 with
                                      | (p1,wl3) ->
                                          let uu____16833 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs"
                                             in
                                          (match uu____16833 with
                                           | (p2,wl4) -> ([p1; p2], wl4))
                                       in
                                    (match uu____16806 with
                                     | (sub_probs,wl3) ->
                                         let uu____16865 =
                                           let uu____16866 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16866  in
                                         solve env1 uu____16865))))
                  in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16900 = FStar_Syntax_Util.head_and_args rhs2  in
                   match uu____16900 with
                   | (uu____16918,args) ->
                       (match args with | [] -> false | uu____16954 -> true)
                    in
                 let is_arrow rhs2 =
                   let uu____16973 =
                     let uu____16974 = FStar_Syntax_Subst.compress rhs2  in
                     uu____16974.FStar_Syntax_Syntax.n  in
                   match uu____16973 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____16978 -> true
                   | uu____16994 -> false  in
                 let uu____16996 = quasi_pattern env1 lhs1  in
                 match uu____16996 with
                 | FStar_Pervasives_Native.None  ->
                     let msg =
                       mklstr
                         (fun uu____17015  ->
                            let uu____17016 = prob_to_string env1 orig1  in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____17016)
                        in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                     let uu____17025 = is_app rhs1  in
                     if uu____17025
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____17030 = is_arrow rhs1  in
                        if uu____17030
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu____17043  ->
                                  let uu____17044 = prob_to_string env1 orig1
                                     in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____17044)
                              in
                           giveup_or_defer env1 orig1 wl1 msg))
                  in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB  ->
                   if wl.defer_ok
                   then
                     let uu____17048 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____17048
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV  ->
                   if wl.defer_ok
                   then
                     let uu____17054 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____17054
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ  ->
                   let uu____17059 = lhs  in
                   (match uu____17059 with
                    | Flex (_t1,ctx_uv,args_lhs) ->
                        let uu____17063 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs
                           in
                        (match uu____17063 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs  in
                             let names_to_string1 fvs =
                               let uu____17081 =
                                 let uu____17085 =
                                   FStar_Util.set_elements fvs  in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____17085
                                  in
                               FStar_All.pipe_right uu____17081
                                 (FStar_String.concat ", ")
                                in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders)
                                in
                             let fvs2 = FStar_Syntax_Free.names rhs1  in
                             let uu____17106 = occurs_check ctx_uv rhs1  in
                             (match uu____17106 with
                              | (uvars,occurs_ok,msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17135 =
                                      let uu____17136 =
                                        let uu____17138 =
                                          FStar_Option.get msg  in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17138
                                         in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17136
                                       in
                                    giveup_or_defer env orig wl uu____17135
                                  else
                                    (let uu____17146 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1
                                        in
                                     if uu____17146
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1
                                          in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars wl
                                          in
                                       let uu____17153 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1
                                          in
                                       solve env uu____17153
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            mklstr
                                              (fun uu____17169  ->
                                                 let uu____17170 =
                                                   names_to_string1 fvs2  in
                                                 let uu____17172 =
                                                   names_to_string1 fvs1  in
                                                 let uu____17174 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders)
                                                    in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17170 uu____17172
                                                   uu____17174)
                                             in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17186 ->
                             if wl.defer_ok
                             then
                               let uu____17190 =
                                 FStar_Thunk.mkv "Not a pattern"  in
                               giveup_or_defer env orig wl uu____17190
                             else
                               (let uu____17195 =
                                  try_quasi_pattern orig env wl lhs rhs  in
                                match uu____17195 with
                                | (FStar_Util.Inr sol,wl1) ->
                                    let uu____17221 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17221
                                | (FStar_Util.Inl msg,uu____17223) ->
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
                  let uu____17241 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17241
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____17247 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17247
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17252 =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs)
                   in
                if uu____17252
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
                    (let uu____17259 =
                       FStar_Thunk.mkv "flex-flex non-pattern"  in
                     giveup_or_defer env orig wl uu____17259)
                  else
                    (let uu____17264 =
                       let uu____17281 = quasi_pattern env lhs  in
                       let uu____17288 = quasi_pattern env rhs  in
                       (uu____17281, uu____17288)  in
                     match uu____17264 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                        (binders_rhs,t_res_rhs)) ->
                         let uu____17331 = lhs  in
                         (match uu____17331 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17332;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17334;_},u_lhs,uu____17336)
                              ->
                              let uu____17339 = rhs  in
                              (match uu____17339 with
                               | Flex (uu____17340,u_rhs,uu____17342) ->
                                   let uu____17343 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs)
                                      in
                                   if uu____17343
                                   then
                                     let uu____17350 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl
                                        in
                                     solve env uu____17350
                                   else
                                     (let uu____17353 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      match uu____17353 with
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
                                          let uu____17385 =
                                            let uu____17392 =
                                              let uu____17395 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs
                                                 in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17395
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
                                              uu____17392
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None
                                             in
                                          (match uu____17385 with
                                           | (uu____17401,w,wl1) ->
                                               let w_app =
                                                 let uu____17405 =
                                                   FStar_List.map
                                                     (fun uu____17416  ->
                                                        match uu____17416
                                                        with
                                                        | (z,uu____17424) ->
                                                            let uu____17429 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____17429) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____17405
                                                   w.FStar_Syntax_Syntax.pos
                                                  in
                                               ((let uu____17431 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17431
                                                 then
                                                   let uu____17436 =
                                                     let uu____17440 =
                                                       flex_t_to_string lhs
                                                        in
                                                     let uu____17442 =
                                                       let uu____17446 =
                                                         flex_t_to_string rhs
                                                          in
                                                       let uu____17448 =
                                                         let uu____17452 =
                                                           term_to_string w
                                                            in
                                                         let uu____17454 =
                                                           let uu____17458 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs)
                                                              in
                                                           let uu____17467 =
                                                             let uu____17471
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                in
                                                             let uu____17480
                                                               =
                                                               let uu____17484
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs
                                                                  in
                                                               [uu____17484]
                                                                in
                                                             uu____17471 ::
                                                               uu____17480
                                                              in
                                                           uu____17458 ::
                                                             uu____17467
                                                            in
                                                         uu____17452 ::
                                                           uu____17454
                                                          in
                                                       uu____17446 ::
                                                         uu____17448
                                                        in
                                                     uu____17440 ::
                                                       uu____17442
                                                      in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17436
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17501 =
                                                       let uu____17506 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs))
                                                          in
                                                       (u_lhs, uu____17506)
                                                        in
                                                     TERM uu____17501  in
                                                   let uu____17507 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                      in
                                                   if uu____17507
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17515 =
                                                          let uu____17520 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_rhs,
                                                            uu____17520)
                                                           in
                                                        TERM uu____17515  in
                                                      [s1; s2])
                                                    in
                                                 let uu____17521 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1
                                                    in
                                                 solve env uu____17521))))))
                     | uu____17522 ->
                         let uu____17539 =
                           FStar_Thunk.mkv "flex-flex: non-patterns"  in
                         giveup_or_defer env orig wl uu____17539)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17593 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17593
            then
              let uu____17598 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17600 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17602 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17604 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17598 uu____17600 uu____17602 uu____17604
            else ());
           (let uu____17615 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17615 with
            | (head1,args1) ->
                let uu____17658 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17658 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17728 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17728 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17733 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17733)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17754 =
                         mklstr
                           (fun uu____17765  ->
                              let uu____17766 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17768 = args_to_string args1  in
                              let uu____17772 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17774 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17766 uu____17768 uu____17772
                                uu____17774)
                          in
                       giveup env1 uu____17754 orig
                     else
                       (let uu____17781 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17786 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17786 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17781
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2602_17790 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2602_17790.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2602_17790.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2602_17790.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2602_17790.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2602_17790.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2602_17790.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2602_17790.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2602_17790.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17800 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17800
                                    else solve env1 wl2))
                        else
                          (let uu____17805 = base_and_refinement env1 t1  in
                           match uu____17805 with
                           | (base1,refinement1) ->
                               let uu____17830 = base_and_refinement env1 t2
                                  in
                               (match uu____17830 with
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
                                           let uu____17995 =
                                             FStar_List.fold_right
                                               (fun uu____18035  ->
                                                  fun uu____18036  ->
                                                    match (uu____18035,
                                                            uu____18036)
                                                    with
                                                    | (((a1,uu____18088),
                                                        (a2,uu____18090)),
                                                       (probs,wl3)) ->
                                                        let uu____18139 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18139
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17995 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18182 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18182
                                                 then
                                                   let uu____18187 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18187
                                                 else ());
                                                (let uu____18193 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18193
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
                                                    (let uu____18220 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18220 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18236 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18236
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18244 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18244))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18269 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18269 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18285 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18285
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18293 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18293)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18321 =
                                           match uu____18321 with
                                           | (prob,reason) ->
                                               ((let uu____18338 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18338
                                                 then
                                                   let uu____18343 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18345 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____18343 uu____18345
                                                 else ());
                                                (let uu____18351 =
                                                   let uu____18360 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18363 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18360, uu____18363)
                                                    in
                                                 match uu____18351 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18376 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18376 with
                                                      | (head1',uu____18394)
                                                          ->
                                                          let uu____18419 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18419
                                                           with
                                                           | (head2',uu____18437)
                                                               ->
                                                               let uu____18462
                                                                 =
                                                                 let uu____18467
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18468
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18467,
                                                                   uu____18468)
                                                                  in
                                                               (match uu____18462
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18470
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18470
                                                                    then
                                                                    let uu____18475
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18477
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18479
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18481
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18475
                                                                    uu____18477
                                                                    uu____18479
                                                                    uu____18481
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18486
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2690_18494
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2690_18494.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2690_18494.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2690_18494.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2690_18494.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2690_18494.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2690_18494.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2690_18494.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2690_18494.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18496
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18496
                                                                    then
                                                                    let uu____18501
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18501
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18506 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18518 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18518 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18526 =
                                             let uu____18527 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18527.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18526 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18532 -> false  in
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
                                          | uu____18535 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18538 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2710_18574 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2710_18574.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2710_18574.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2710_18574.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2710_18574.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2710_18574.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2710_18574.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2710_18574.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2710_18574.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18650 = destruct_flex_t scrutinee wl1  in
             match uu____18650 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____18661 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18661 with
                  | (xs,pat_term,uu____18677,uu____18678) ->
                      let uu____18683 =
                        FStar_List.fold_left
                          (fun uu____18706  ->
                             fun x  ->
                               match uu____18706 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18727 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18727 with
                                    | (uu____18746,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18683 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18767 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18767 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2751_18784 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2751_18784.wl_deferred_to_tac);
                                    ctr = (uu___2751_18784.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2751_18784.umax_heuristic_ok);
                                    tcenv = (uu___2751_18784.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2751_18784.repr_subcomp_allowed)
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18795 = solve env1 wl'  in
                                (match uu____18795 with
                                 | Success (uu____18798,defer_to_tac,imps) ->
                                     let wl'1 =
                                       let uu___2760_18802 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2760_18802.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2760_18802.wl_deferred_to_tac);
                                         ctr = (uu___2760_18802.ctr);
                                         defer_ok =
                                           (uu___2760_18802.defer_ok);
                                         smt_ok = (uu___2760_18802.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2760_18802.umax_heuristic_ok);
                                         tcenv = (uu___2760_18802.tcenv);
                                         wl_implicits =
                                           (uu___2760_18802.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2760_18802.repr_subcomp_allowed)
                                       }  in
                                     let uu____18803 = solve env1 wl'1  in
                                     (match uu____18803 with
                                      | Success
                                          (uu____18806,defer_to_tac',imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18810 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps')
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____18810))
                                      | Failed uu____18816 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18822 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18845 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18845
                 then
                   let uu____18850 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18852 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18850 uu____18852
                 else ());
                (let uu____18857 =
                   let uu____18878 =
                     let uu____18887 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18887)  in
                   let uu____18894 =
                     let uu____18903 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18903)  in
                   (uu____18878, uu____18894)  in
                 match uu____18857 with
                 | ((uu____18933,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18936;
                                   FStar_Syntax_Syntax.vars = uu____18937;_}),
                    (s,t)) ->
                     let uu____19008 =
                       let uu____19010 = is_flex scrutinee  in
                       Prims.op_Negation uu____19010  in
                     if uu____19008
                     then
                       ((let uu____19021 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19021
                         then
                           let uu____19026 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19026
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19045 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19045
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19060 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19060
                           then
                             let uu____19065 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19067 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19065 uu____19067
                           else ());
                          (let pat_discriminates uu___26_19092 =
                             match uu___26_19092 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19108;
                                  FStar_Syntax_Syntax.p = uu____19109;_},FStar_Pervasives_Native.None
                                ,uu____19110) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19124;
                                  FStar_Syntax_Syntax.p = uu____19125;_},FStar_Pervasives_Native.None
                                ,uu____19126) -> true
                             | uu____19153 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19256 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19256 with
                                       | (uu____19258,uu____19259,t') ->
                                           let uu____19277 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19277 with
                                            | (FullMatch ,uu____19289) ->
                                                true
                                            | (HeadMatch
                                               uu____19303,uu____19304) ->
                                                true
                                            | uu____19319 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19356 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19356
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19367 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19367 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19455,uu____19456) ->
                                       branches1
                                   | uu____19601 -> branches  in
                                 let uu____19656 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19665 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19665 with
                                        | (p,uu____19669,uu____19670) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19699  ->
                                      FStar_Util.Inr uu____19699) uu____19656))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19729 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19729 with
                                | (p,uu____19738,e) ->
                                    ((let uu____19757 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19757
                                      then
                                        let uu____19762 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19764 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19762 uu____19764
                                      else ());
                                     (let uu____19769 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19784  ->
                                           FStar_Util.Inr uu____19784)
                                        uu____19769)))))
                 | ((s,t),(uu____19787,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19790;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19791;_}))
                     ->
                     let uu____19860 =
                       let uu____19862 = is_flex scrutinee  in
                       Prims.op_Negation uu____19862  in
                     if uu____19860
                     then
                       ((let uu____19873 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19873
                         then
                           let uu____19878 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19878
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19897 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19897
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19912 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19912
                           then
                             let uu____19917 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19919 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19917 uu____19919
                           else ());
                          (let pat_discriminates uu___26_19944 =
                             match uu___26_19944 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19960;
                                  FStar_Syntax_Syntax.p = uu____19961;_},FStar_Pervasives_Native.None
                                ,uu____19962) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19976;
                                  FStar_Syntax_Syntax.p = uu____19977;_},FStar_Pervasives_Native.None
                                ,uu____19978) -> true
                             | uu____20005 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20108 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20108 with
                                       | (uu____20110,uu____20111,t') ->
                                           let uu____20129 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20129 with
                                            | (FullMatch ,uu____20141) ->
                                                true
                                            | (HeadMatch
                                               uu____20155,uu____20156) ->
                                                true
                                            | uu____20171 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20208 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20208
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20219 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20219 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20307,uu____20308) ->
                                       branches1
                                   | uu____20453 -> branches  in
                                 let uu____20508 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20517 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20517 with
                                        | (p,uu____20521,uu____20522) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____20551  ->
                                      FStar_Util.Inr uu____20551) uu____20508))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20581 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20581 with
                                | (p,uu____20590,e) ->
                                    ((let uu____20609 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20609
                                      then
                                        let uu____20614 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20616 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20614 uu____20616
                                      else ());
                                     (let uu____20621 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____20636  ->
                                           FStar_Util.Inr uu____20636)
                                        uu____20621)))))
                 | uu____20637 ->
                     ((let uu____20659 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20659
                       then
                         let uu____20664 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20666 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20664 uu____20666
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20712 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20712
            then
              let uu____20717 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20719 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20721 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20723 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20717 uu____20719 uu____20721 uu____20723
            else ());
           (let uu____20728 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20728 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20759,uu____20760) ->
                     let rec may_relate head =
                       let uu____20788 =
                         let uu____20789 = FStar_Syntax_Subst.compress head
                            in
                         uu____20789.FStar_Syntax_Syntax.n  in
                       match uu____20788 with
                       | FStar_Syntax_Syntax.Tm_name uu____20793 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20795 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20820 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20820 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20822 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20825
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20826 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20829,uu____20830) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20872) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20878) ->
                           may_relate t
                       | uu____20883 -> false  in
                     let uu____20885 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20885 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20898 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20898
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20908 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20908
                          then
                            let uu____20911 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20911 with
                             | (guard,wl2) ->
                                 let uu____20918 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20918)
                          else
                            (let uu____20921 =
                               mklstr
                                 (fun uu____20932  ->
                                    let uu____20933 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20935 =
                                      let uu____20937 =
                                        let uu____20941 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20941
                                          (fun x  ->
                                             let uu____20948 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20948)
                                         in
                                      FStar_Util.dflt "" uu____20937  in
                                    let uu____20953 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20955 =
                                      let uu____20957 =
                                        let uu____20961 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20961
                                          (fun x  ->
                                             let uu____20968 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20968)
                                         in
                                      FStar_Util.dflt "" uu____20957  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20933 uu____20935 uu____20953
                                      uu____20955)
                                in
                             giveup env1 uu____20921 orig))
                 | (HeadMatch (true ),uu____20974) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20989 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20989 with
                        | (guard,wl2) ->
                            let uu____20996 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20996)
                     else
                       (let uu____20999 =
                          mklstr
                            (fun uu____21006  ->
                               let uu____21007 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____21009 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____21007 uu____21009)
                           in
                        giveup env1 uu____20999 orig)
                 | (uu____21012,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2942_21026 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2942_21026.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2942_21026.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2942_21026.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2942_21026.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2942_21026.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2942_21026.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2942_21026.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2942_21026.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____21053 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____21053
          then
            let uu____21056 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____21056
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____21062 =
                let uu____21065 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21065  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____21062 t1);
             (let uu____21084 =
                let uu____21087 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21087  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____21084 t2);
             (let uu____21106 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____21106
              then
                let uu____21110 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____21112 =
                  let uu____21114 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____21116 =
                    let uu____21118 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____21118  in
                  Prims.op_Hat uu____21114 uu____21116  in
                let uu____21121 =
                  let uu____21123 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____21125 =
                    let uu____21127 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____21127  in
                  Prims.op_Hat uu____21123 uu____21125  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21110 uu____21112 uu____21121
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21134,uu____21135) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21151,FStar_Syntax_Syntax.Tm_delayed uu____21152) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21168,uu____21169) ->
                  let uu____21196 =
                    let uu___2973_21197 = problem  in
                    let uu____21198 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2973_21197.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21198;
                      FStar_TypeChecker_Common.relation =
                        (uu___2973_21197.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2973_21197.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2973_21197.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2973_21197.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2973_21197.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2973_21197.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2973_21197.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2973_21197.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21196 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21199,uu____21200) ->
                  let uu____21207 =
                    let uu___2979_21208 = problem  in
                    let uu____21209 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2979_21208.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21209;
                      FStar_TypeChecker_Common.relation =
                        (uu___2979_21208.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2979_21208.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2979_21208.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2979_21208.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2979_21208.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2979_21208.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2979_21208.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2979_21208.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21207 wl
              | (uu____21210,FStar_Syntax_Syntax.Tm_ascribed uu____21211) ->
                  let uu____21238 =
                    let uu___2985_21239 = problem  in
                    let uu____21240 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2985_21239.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2985_21239.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2985_21239.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21240;
                      FStar_TypeChecker_Common.element =
                        (uu___2985_21239.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2985_21239.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2985_21239.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2985_21239.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2985_21239.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2985_21239.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21238 wl
              | (uu____21241,FStar_Syntax_Syntax.Tm_meta uu____21242) ->
                  let uu____21249 =
                    let uu___2991_21250 = problem  in
                    let uu____21251 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2991_21250.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2991_21250.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2991_21250.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21251;
                      FStar_TypeChecker_Common.element =
                        (uu___2991_21250.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2991_21250.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2991_21250.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2991_21250.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2991_21250.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2991_21250.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21249 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21253),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21255)) ->
                  let uu____21264 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21264
              | (FStar_Syntax_Syntax.Tm_bvar uu____21265,uu____21266) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21268,FStar_Syntax_Syntax.Tm_bvar uu____21269) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___27_21339 =
                    match uu___27_21339 with
                    | [] -> c
                    | bs ->
                        let uu____21367 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21367
                     in
                  let uu____21378 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21378 with
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
                                    let uu____21527 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21527
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
                  let mk_t t l uu___28_21616 =
                    match uu___28_21616 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21658 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21658 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21803 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21804 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21803
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21804 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21806,uu____21807) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21838 -> true
                    | uu____21858 -> false  in
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
                      (let uu____21918 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3093_21926 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3093_21926.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3093_21926.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3093_21926.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3093_21926.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3093_21926.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3093_21926.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3093_21926.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3093_21926.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3093_21926.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3093_21926.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3093_21926.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3093_21926.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3093_21926.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3093_21926.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3093_21926.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3093_21926.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3093_21926.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3093_21926.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3093_21926.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3093_21926.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3093_21926.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3093_21926.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3093_21926.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3093_21926.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3093_21926.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3093_21926.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3093_21926.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3093_21926.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3093_21926.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3093_21926.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3093_21926.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3093_21926.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3093_21926.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3093_21926.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3093_21926.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3093_21926.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3093_21926.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3093_21926.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3093_21926.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3093_21926.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3093_21926.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3093_21926.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3093_21926.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3093_21926.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____21918 with
                       | (uu____21931,ty,uu____21933) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21942 =
                                 let uu____21943 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21943.FStar_Syntax_Syntax.n  in
                               match uu____21942 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21946 ->
                                   let uu____21953 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21953
                               | uu____21954 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21957 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21957
                             then
                               let uu____21962 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21964 =
                                 let uu____21966 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21966
                                  in
                               let uu____21967 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21962 uu____21964 uu____21967
                             else ());
                            r1))
                     in
                  let uu____21972 =
                    let uu____21989 = maybe_eta t1  in
                    let uu____21996 = maybe_eta t2  in
                    (uu____21989, uu____21996)  in
                  (match uu____21972 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3114_22038 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3114_22038.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3114_22038.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3114_22038.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3114_22038.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3114_22038.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3114_22038.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3114_22038.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3114_22038.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22059 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22059
                       then
                         let uu____22062 = destruct_flex_t not_abs wl  in
                         (match uu____22062 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3131_22079 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3131_22079.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3131_22079.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3131_22079.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3131_22079.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3131_22079.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3131_22079.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3131_22079.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3131_22079.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22082 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22082 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22105 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22105
                       then
                         let uu____22108 = destruct_flex_t not_abs wl  in
                         (match uu____22108 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3131_22125 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3131_22125.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3131_22125.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3131_22125.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3131_22125.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3131_22125.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3131_22125.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3131_22125.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3131_22125.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22128 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22128 orig))
                   | uu____22131 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22149,FStar_Syntax_Syntax.Tm_abs uu____22150) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22181 -> true
                    | uu____22201 -> false  in
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
                      (let uu____22261 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3093_22269 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3093_22269.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3093_22269.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3093_22269.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3093_22269.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3093_22269.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3093_22269.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3093_22269.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3093_22269.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3093_22269.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3093_22269.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3093_22269.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3093_22269.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3093_22269.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3093_22269.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3093_22269.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3093_22269.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3093_22269.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3093_22269.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3093_22269.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3093_22269.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3093_22269.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3093_22269.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3093_22269.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3093_22269.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3093_22269.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3093_22269.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3093_22269.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3093_22269.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3093_22269.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3093_22269.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3093_22269.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3093_22269.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3093_22269.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3093_22269.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3093_22269.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3093_22269.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3093_22269.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3093_22269.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3093_22269.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3093_22269.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3093_22269.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3093_22269.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3093_22269.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3093_22269.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____22261 with
                       | (uu____22274,ty,uu____22276) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22285 =
                                 let uu____22286 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22286.FStar_Syntax_Syntax.n  in
                               match uu____22285 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22289 ->
                                   let uu____22296 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22296
                               | uu____22297 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22300 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22300
                             then
                               let uu____22305 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22307 =
                                 let uu____22309 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22309
                                  in
                               let uu____22310 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22305 uu____22307 uu____22310
                             else ());
                            r1))
                     in
                  let uu____22315 =
                    let uu____22332 = maybe_eta t1  in
                    let uu____22339 = maybe_eta t2  in
                    (uu____22332, uu____22339)  in
                  (match uu____22315 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3114_22381 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3114_22381.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3114_22381.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3114_22381.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3114_22381.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3114_22381.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3114_22381.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3114_22381.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3114_22381.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22402 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22402
                       then
                         let uu____22405 = destruct_flex_t not_abs wl  in
                         (match uu____22405 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3131_22422 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3131_22422.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3131_22422.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3131_22422.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3131_22422.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3131_22422.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3131_22422.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3131_22422.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3131_22422.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22425 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22425 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22448 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22448
                       then
                         let uu____22451 = destruct_flex_t not_abs wl  in
                         (match uu____22451 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3131_22468 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3131_22468.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3131_22468.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3131_22468.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3131_22468.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3131_22468.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3131_22468.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3131_22468.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3131_22468.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22471 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22471 orig))
                   | uu____22474 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22504 =
                    let uu____22509 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22509 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3154_22537 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3154_22537.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3154_22537.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3156_22539 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3156_22539.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3156_22539.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22540,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3154_22555 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3154_22555.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3154_22555.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3156_22557 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3156_22557.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3156_22557.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22558 -> (x1, x2)  in
                  (match uu____22504 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22577 = as_refinement false env t11  in
                       (match uu____22577 with
                        | (x12,phi11) ->
                            let uu____22585 = as_refinement false env t21  in
                            (match uu____22585 with
                             | (x22,phi21) ->
                                 ((let uu____22594 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22594
                                   then
                                     ((let uu____22599 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22601 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22603 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22599
                                         uu____22601 uu____22603);
                                      (let uu____22606 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22608 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22610 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22606
                                         uu____22608 uu____22610))
                                   else ());
                                  (let uu____22615 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22615 with
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
                                         let uu____22686 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22686
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22698 =
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
                                         (let uu____22711 =
                                            let uu____22714 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22714
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22711
                                            (p_guard base_prob));
                                         (let uu____22733 =
                                            let uu____22736 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22736
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22733
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22755 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22755)
                                          in
                                       let has_uvars =
                                         (let uu____22760 =
                                            let uu____22762 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22762
                                             in
                                          Prims.op_Negation uu____22760) ||
                                           (let uu____22766 =
                                              let uu____22768 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22768
                                               in
                                            Prims.op_Negation uu____22766)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22772 =
                                           let uu____22777 =
                                             let uu____22786 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22786]  in
                                           mk_t_problem wl1 uu____22777 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22772 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22809 =
                                                solve env1
                                                  (let uu___3199_22811 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3199_22811.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3199_22811.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3199_22811.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3199_22811.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3199_22811.tcenv);
                                                     wl_implicits =
                                                       (uu___3199_22811.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3199_22811.repr_subcomp_allowed)
                                                   })
                                                 in
                                              (match uu____22809 with
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
                                                   (uu____22826,defer_to_tac,uu____22828)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22833 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22833
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3215_22842 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3215_22842.attempting);
                                                         wl_deferred =
                                                           (uu___3215_22842.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3215_22842.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3215_22842.defer_ok);
                                                         smt_ok =
                                                           (uu___3215_22842.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3215_22842.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3215_22842.tcenv);
                                                         wl_implicits =
                                                           (uu___3215_22842.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3215_22842.repr_subcomp_allowed)
                                                       }  in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac []
                                                        in
                                                     let uu____22845 =
                                                       attempt [base_prob]
                                                         wl5
                                                        in
                                                     solve env1 uu____22845))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22848,FStar_Syntax_Syntax.Tm_uvar uu____22849) ->
                  let uu____22874 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22874 with
                   | (t11,wl1) ->
                       let uu____22881 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22881 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22890;
                    FStar_Syntax_Syntax.pos = uu____22891;
                    FStar_Syntax_Syntax.vars = uu____22892;_},uu____22893),FStar_Syntax_Syntax.Tm_uvar
                 uu____22894) ->
                  let uu____22943 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22943 with
                   | (t11,wl1) ->
                       let uu____22950 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22950 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22959,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22960;
                    FStar_Syntax_Syntax.pos = uu____22961;
                    FStar_Syntax_Syntax.vars = uu____22962;_},uu____22963))
                  ->
                  let uu____23012 = ensure_no_uvar_subst t1 wl  in
                  (match uu____23012 with
                   | (t11,wl1) ->
                       let uu____23019 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____23019 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23028;
                    FStar_Syntax_Syntax.pos = uu____23029;
                    FStar_Syntax_Syntax.vars = uu____23030;_},uu____23031),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23032;
                    FStar_Syntax_Syntax.pos = uu____23033;
                    FStar_Syntax_Syntax.vars = uu____23034;_},uu____23035))
                  ->
                  let uu____23108 = ensure_no_uvar_subst t1 wl  in
                  (match uu____23108 with
                   | (t11,wl1) ->
                       let uu____23115 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____23115 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23124,uu____23125) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23138 = destruct_flex_t t1 wl  in
                  (match uu____23138 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23145;
                    FStar_Syntax_Syntax.pos = uu____23146;
                    FStar_Syntax_Syntax.vars = uu____23147;_},uu____23148),uu____23149)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23186 = destruct_flex_t t1 wl  in
                  (match uu____23186 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23193,FStar_Syntax_Syntax.Tm_uvar uu____23194) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23207,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23208;
                    FStar_Syntax_Syntax.pos = uu____23209;
                    FStar_Syntax_Syntax.vars = uu____23210;_},uu____23211))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23248,FStar_Syntax_Syntax.Tm_arrow uu____23249) ->
                  solve_t' env
                    (let uu___3318_23277 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3318_23277.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3318_23277.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3318_23277.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3318_23277.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3318_23277.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3318_23277.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3318_23277.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3318_23277.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3318_23277.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23278;
                    FStar_Syntax_Syntax.pos = uu____23279;
                    FStar_Syntax_Syntax.vars = uu____23280;_},uu____23281),FStar_Syntax_Syntax.Tm_arrow
                 uu____23282) ->
                  solve_t' env
                    (let uu___3318_23334 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3318_23334.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3318_23334.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3318_23334.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3318_23334.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3318_23334.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3318_23334.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3318_23334.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3318_23334.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3318_23334.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23335,FStar_Syntax_Syntax.Tm_uvar uu____23336) ->
                  let uu____23349 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23349
              | (uu____23350,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23351;
                    FStar_Syntax_Syntax.pos = uu____23352;
                    FStar_Syntax_Syntax.vars = uu____23353;_},uu____23354))
                  ->
                  let uu____23391 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23391
              | (FStar_Syntax_Syntax.Tm_uvar uu____23392,uu____23393) ->
                  let uu____23406 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23406
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23407;
                    FStar_Syntax_Syntax.pos = uu____23408;
                    FStar_Syntax_Syntax.vars = uu____23409;_},uu____23410),uu____23411)
                  ->
                  let uu____23448 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23448
              | (FStar_Syntax_Syntax.Tm_refine uu____23449,uu____23450) ->
                  let t21 =
                    let uu____23458 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23458  in
                  solve_t env
                    (let uu___3353_23484 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3353_23484.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3353_23484.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3353_23484.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3353_23484.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3353_23484.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3353_23484.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3353_23484.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3353_23484.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3353_23484.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23485,FStar_Syntax_Syntax.Tm_refine uu____23486) ->
                  let t11 =
                    let uu____23494 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23494  in
                  solve_t env
                    (let uu___3360_23520 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3360_23520.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3360_23520.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3360_23520.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3360_23520.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3360_23520.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3360_23520.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3360_23520.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3360_23520.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3360_23520.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23602 =
                    let uu____23603 = guard_of_prob env wl problem t1 t2  in
                    match uu____23603 with
                    | (guard,wl1) ->
                        let uu____23610 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23610
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23829 = br1  in
                        (match uu____23829 with
                         | (p1,w1,uu____23858) ->
                             let uu____23875 = br2  in
                             (match uu____23875 with
                              | (p2,w2,uu____23898) ->
                                  let uu____23903 =
                                    let uu____23905 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23905  in
                                  if uu____23903
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23932 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23932 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23969 = br2  in
                                         (match uu____23969 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____24002 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____24002
                                                 in
                                              let uu____24007 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____24038,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____24059) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____24118 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____24118 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____24007
                                                (fun uu____24190  ->
                                                   match uu____24190 with
                                                   | (wprobs,wl2) ->
                                                       let uu____24227 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____24227
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24248
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24248
                                                              then
                                                                let uu____24253
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24255
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24253
                                                                  uu____24255
                                                              else ());
                                                             (let uu____24261
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24261
                                                                (fun
                                                                   uu____24297
                                                                    ->
                                                                   match uu____24297
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
                    | uu____24426 -> FStar_Pervasives_Native.None  in
                  let uu____24467 = solve_branches wl brs1 brs2  in
                  (match uu____24467 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24493 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24493 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24520 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24520 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24554 =
                                FStar_List.map
                                  (fun uu____24566  ->
                                     match uu____24566 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24554  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24575 =
                              let uu____24576 =
                                let uu____24577 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24577
                                  (let uu___3459_24585 = wl3  in
                                   {
                                     attempting =
                                       (uu___3459_24585.attempting);
                                     wl_deferred =
                                       (uu___3459_24585.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3459_24585.wl_deferred_to_tac);
                                     ctr = (uu___3459_24585.ctr);
                                     defer_ok = (uu___3459_24585.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3459_24585.umax_heuristic_ok);
                                     tcenv = (uu___3459_24585.tcenv);
                                     wl_implicits =
                                       (uu___3459_24585.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3459_24585.repr_subcomp_allowed)
                                   })
                                 in
                              solve env uu____24576  in
                            (match uu____24575 with
                             | Success (ds,ds',imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24591 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24600 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24600 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24603,uu____24604) ->
                  let head1 =
                    let uu____24628 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24628
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24674 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24674
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24720 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24720
                    then
                      let uu____24724 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24726 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24728 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24724 uu____24726 uu____24728
                    else ());
                   (let no_free_uvars t =
                      (let uu____24742 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24742) &&
                        (let uu____24746 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24746)
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
                      let uu____24765 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24765 = FStar_Syntax_Util.Equal  in
                    let uu____24766 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24766
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24770 = equal t1 t2  in
                         (if uu____24770
                          then
                            let uu____24773 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24773
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24778 =
                            let uu____24785 = equal t1 t2  in
                            if uu____24785
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24798 = mk_eq2 wl env orig t1 t2  in
                               match uu____24798 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24778 with
                          | (guard,wl1) ->
                              let uu____24819 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24819))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24822,uu____24823) ->
                  let head1 =
                    let uu____24831 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24831
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24877 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24877
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24923 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24923
                    then
                      let uu____24927 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24929 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24931 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24927 uu____24929 uu____24931
                    else ());
                   (let no_free_uvars t =
                      (let uu____24945 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24945) &&
                        (let uu____24949 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24949)
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
                      let uu____24968 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24968 = FStar_Syntax_Util.Equal  in
                    let uu____24969 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24969
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24973 = equal t1 t2  in
                         (if uu____24973
                          then
                            let uu____24976 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24976
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24981 =
                            let uu____24988 = equal t1 t2  in
                            if uu____24988
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25001 = mk_eq2 wl env orig t1 t2  in
                               match uu____25001 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24981 with
                          | (guard,wl1) ->
                              let uu____25022 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25022))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____25025,uu____25026) ->
                  let head1 =
                    let uu____25028 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25028
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25074 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25074
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25120 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25120
                    then
                      let uu____25124 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25126 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25128 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25124 uu____25126 uu____25128
                    else ());
                   (let no_free_uvars t =
                      (let uu____25142 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25142) &&
                        (let uu____25146 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25146)
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
                      let uu____25165 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25165 = FStar_Syntax_Util.Equal  in
                    let uu____25166 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25166
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25170 = equal t1 t2  in
                         (if uu____25170
                          then
                            let uu____25173 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25173
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25178 =
                            let uu____25185 = equal t1 t2  in
                            if uu____25185
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25198 = mk_eq2 wl env orig t1 t2  in
                               match uu____25198 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25178 with
                          | (guard,wl1) ->
                              let uu____25219 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25219))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25222,uu____25223) ->
                  let head1 =
                    let uu____25225 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25225
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25271 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25271
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25317 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25317
                    then
                      let uu____25321 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25323 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25325 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25321 uu____25323 uu____25325
                    else ());
                   (let no_free_uvars t =
                      (let uu____25339 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25339) &&
                        (let uu____25343 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25343)
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
                      let uu____25362 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25362 = FStar_Syntax_Util.Equal  in
                    let uu____25363 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25363
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25367 = equal t1 t2  in
                         (if uu____25367
                          then
                            let uu____25370 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25370
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25375 =
                            let uu____25382 = equal t1 t2  in
                            if uu____25382
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25395 = mk_eq2 wl env orig t1 t2  in
                               match uu____25395 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25375 with
                          | (guard,wl1) ->
                              let uu____25416 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25416))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25419,uu____25420) ->
                  let head1 =
                    let uu____25422 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25422
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25462 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25462
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25502 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25502
                    then
                      let uu____25506 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25508 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25510 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25506 uu____25508 uu____25510
                    else ());
                   (let no_free_uvars t =
                      (let uu____25524 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25524) &&
                        (let uu____25528 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25528)
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
                      let uu____25547 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25547 = FStar_Syntax_Util.Equal  in
                    let uu____25548 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25548
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25552 = equal t1 t2  in
                         (if uu____25552
                          then
                            let uu____25555 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25555
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25560 =
                            let uu____25567 = equal t1 t2  in
                            if uu____25567
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25580 = mk_eq2 wl env orig t1 t2  in
                               match uu____25580 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25560 with
                          | (guard,wl1) ->
                              let uu____25601 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25601))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25604,uu____25605) ->
                  let head1 =
                    let uu____25623 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25623
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25663 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25663
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25703 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25703
                    then
                      let uu____25707 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25709 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25711 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25707 uu____25709 uu____25711
                    else ());
                   (let no_free_uvars t =
                      (let uu____25725 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25725) &&
                        (let uu____25729 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25729)
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
                      let uu____25748 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25748 = FStar_Syntax_Util.Equal  in
                    let uu____25749 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25749
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25753 = equal t1 t2  in
                         (if uu____25753
                          then
                            let uu____25756 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25756
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25761 =
                            let uu____25768 = equal t1 t2  in
                            if uu____25768
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25781 = mk_eq2 wl env orig t1 t2  in
                               match uu____25781 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25761 with
                          | (guard,wl1) ->
                              let uu____25802 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25802))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25805,FStar_Syntax_Syntax.Tm_match uu____25806) ->
                  let head1 =
                    let uu____25830 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25830
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25870 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25870
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25910 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25910
                    then
                      let uu____25914 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25916 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25918 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25914 uu____25916 uu____25918
                    else ());
                   (let no_free_uvars t =
                      (let uu____25932 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25932) &&
                        (let uu____25936 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25936)
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
                      let uu____25955 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25955 = FStar_Syntax_Util.Equal  in
                    let uu____25956 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25956
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25960 = equal t1 t2  in
                         (if uu____25960
                          then
                            let uu____25963 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25963
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25968 =
                            let uu____25975 = equal t1 t2  in
                            if uu____25975
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25988 = mk_eq2 wl env orig t1 t2  in
                               match uu____25988 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25968 with
                          | (guard,wl1) ->
                              let uu____26009 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26009))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26012,FStar_Syntax_Syntax.Tm_uinst uu____26013) ->
                  let head1 =
                    let uu____26021 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26021
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26061 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26061
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26101 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26101
                    then
                      let uu____26105 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26107 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26109 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26105 uu____26107 uu____26109
                    else ());
                   (let no_free_uvars t =
                      (let uu____26123 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26123) &&
                        (let uu____26127 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26127)
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
                      let uu____26146 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26146 = FStar_Syntax_Util.Equal  in
                    let uu____26147 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26147
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26151 = equal t1 t2  in
                         (if uu____26151
                          then
                            let uu____26154 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26154
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26159 =
                            let uu____26166 = equal t1 t2  in
                            if uu____26166
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26179 = mk_eq2 wl env orig t1 t2  in
                               match uu____26179 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26159 with
                          | (guard,wl1) ->
                              let uu____26200 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26200))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26203,FStar_Syntax_Syntax.Tm_name uu____26204) ->
                  let head1 =
                    let uu____26206 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26206
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26246 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26246
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26286 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26286
                    then
                      let uu____26290 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26292 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26294 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26290 uu____26292 uu____26294
                    else ());
                   (let no_free_uvars t =
                      (let uu____26308 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26308) &&
                        (let uu____26312 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26312)
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
                      let uu____26331 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26331 = FStar_Syntax_Util.Equal  in
                    let uu____26332 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26332
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26336 = equal t1 t2  in
                         (if uu____26336
                          then
                            let uu____26339 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26339
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26344 =
                            let uu____26351 = equal t1 t2  in
                            if uu____26351
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26364 = mk_eq2 wl env orig t1 t2  in
                               match uu____26364 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26344 with
                          | (guard,wl1) ->
                              let uu____26385 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26385))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26388,FStar_Syntax_Syntax.Tm_constant uu____26389) ->
                  let head1 =
                    let uu____26391 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26391
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26431 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26431
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26471 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26471
                    then
                      let uu____26475 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26477 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26479 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26475 uu____26477 uu____26479
                    else ());
                   (let no_free_uvars t =
                      (let uu____26493 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26493) &&
                        (let uu____26497 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26497)
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
                      let uu____26516 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26516 = FStar_Syntax_Util.Equal  in
                    let uu____26517 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26517
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26521 = equal t1 t2  in
                         (if uu____26521
                          then
                            let uu____26524 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26524
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26529 =
                            let uu____26536 = equal t1 t2  in
                            if uu____26536
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26549 = mk_eq2 wl env orig t1 t2  in
                               match uu____26549 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26529 with
                          | (guard,wl1) ->
                              let uu____26570 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26570))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26573,FStar_Syntax_Syntax.Tm_fvar uu____26574) ->
                  let head1 =
                    let uu____26576 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26576
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26622 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26622
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26668 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26668
                    then
                      let uu____26672 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26674 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26676 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26672 uu____26674 uu____26676
                    else ());
                   (let no_free_uvars t =
                      (let uu____26690 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26690) &&
                        (let uu____26694 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26694)
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
                      let uu____26713 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26713 = FStar_Syntax_Util.Equal  in
                    let uu____26714 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26714
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26718 = equal t1 t2  in
                         (if uu____26718
                          then
                            let uu____26721 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26721
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26726 =
                            let uu____26733 = equal t1 t2  in
                            if uu____26733
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26746 = mk_eq2 wl env orig t1 t2  in
                               match uu____26746 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26726 with
                          | (guard,wl1) ->
                              let uu____26767 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26767))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26770,FStar_Syntax_Syntax.Tm_app uu____26771) ->
                  let head1 =
                    let uu____26789 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26789
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26829 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26829
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26869 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26869
                    then
                      let uu____26873 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26875 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26877 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26873 uu____26875 uu____26877
                    else ());
                   (let no_free_uvars t =
                      (let uu____26891 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26891) &&
                        (let uu____26895 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26895)
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
                      let uu____26914 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26914 = FStar_Syntax_Util.Equal  in
                    let uu____26915 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26915
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26919 = equal t1 t2  in
                         (if uu____26919
                          then
                            let uu____26922 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26922
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26927 =
                            let uu____26934 = equal t1 t2  in
                            if uu____26934
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26947 = mk_eq2 wl env orig t1 t2  in
                               match uu____26947 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26927 with
                          | (guard,wl1) ->
                              let uu____26968 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26968))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26971,FStar_Syntax_Syntax.Tm_let uu____26972) ->
                  let uu____26999 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26999
                  then
                    let uu____27002 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____27002
                  else
                    (let uu____27005 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____27005 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____27008,uu____27009) ->
                  let uu____27023 =
                    let uu____27029 =
                      let uu____27031 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____27033 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____27035 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____27037 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27031 uu____27033 uu____27035 uu____27037
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27029)
                     in
                  FStar_Errors.raise_error uu____27023
                    t1.FStar_Syntax_Syntax.pos
              | (uu____27041,FStar_Syntax_Syntax.Tm_let uu____27042) ->
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
              | uu____27074 ->
                  let uu____27079 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____27079 orig))))

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
          (let uu____27145 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____27145
           then
             let uu____27150 =
               let uu____27152 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____27152  in
             let uu____27153 =
               let uu____27155 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____27155  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27150 uu____27153
           else ());
          (let uu____27159 =
             let uu____27161 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____27161  in
           if uu____27159
           then
             let uu____27164 =
               mklstr
                 (fun uu____27171  ->
                    let uu____27172 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____27174 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27172 uu____27174)
                in
             giveup env uu____27164 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27196 =
                  mklstr
                    (fun uu____27203  ->
                       let uu____27204 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27206 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27204 uu____27206)
                   in
                giveup env uu____27196 orig)
             else
               (let uu____27211 =
                  FStar_List.fold_left2
                    (fun uu____27232  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27232 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27253 =
                                 let uu____27258 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27259 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27258
                                   FStar_TypeChecker_Common.EQ uu____27259
                                   "effect universes"
                                  in
                               (match uu____27253 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27211 with
                | (univ_sub_probs,wl1) ->
                    let uu____27279 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27279 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27287 =
                           FStar_List.fold_right2
                             (fun uu____27324  ->
                                fun uu____27325  ->
                                  fun uu____27326  ->
                                    match (uu____27324, uu____27325,
                                            uu____27326)
                                    with
                                    | ((a1,uu____27370),(a2,uu____27372),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27405 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27405 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27287 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27432 =
                                  let uu____27435 =
                                    let uu____27438 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27438
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27435
                                   in
                                FStar_List.append univ_sub_probs uu____27432
                                 in
                              let guard =
                                let guard =
                                  let uu____27460 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27460  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3612_27469 = wl3  in
                                {
                                  attempting = (uu___3612_27469.attempting);
                                  wl_deferred = (uu___3612_27469.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3612_27469.wl_deferred_to_tac);
                                  ctr = (uu___3612_27469.ctr);
                                  defer_ok = (uu___3612_27469.defer_ok);
                                  smt_ok = (uu___3612_27469.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3612_27469.umax_heuristic_ok);
                                  tcenv = (uu___3612_27469.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3612_27469.repr_subcomp_allowed)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27471 = attempt sub_probs wl5  in
                              solve env uu____27471))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____27489 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____27489
           then
             let uu____27494 =
               let uu____27496 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27496
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27498 =
               let uu____27500 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27500
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27494 uu____27498
           else ());
          (let uu____27505 =
             let uu____27510 =
               let uu____27515 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27515
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27510
               (fun uu____27532  ->
                  match uu____27532 with
                  | (c,g) ->
                      let uu____27543 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27543, g))
              in
           match uu____27505 with
           | (c12,g_lift) ->
               ((let uu____27547 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27547
                 then
                   let uu____27552 =
                     let uu____27554 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27554
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27556 =
                     let uu____27558 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27558
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27552 uu____27556
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3632_27568 = wl  in
                     {
                       attempting = (uu___3632_27568.attempting);
                       wl_deferred = (uu___3632_27568.wl_deferred);
                       wl_deferred_to_tac =
                         (uu___3632_27568.wl_deferred_to_tac);
                       ctr = (uu___3632_27568.ctr);
                       defer_ok = (uu___3632_27568.defer_ok);
                       smt_ok = (uu___3632_27568.smt_ok);
                       umax_heuristic_ok =
                         (uu___3632_27568.umax_heuristic_ok);
                       tcenv = (uu___3632_27568.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits);
                       repr_subcomp_allowed =
                         (uu___3632_27568.repr_subcomp_allowed)
                     }  in
                   let uu____27569 =
                     let rec is_uvar t =
                       let uu____27583 =
                         let uu____27584 = FStar_Syntax_Subst.compress t  in
                         uu____27584.FStar_Syntax_Syntax.n  in
                       match uu____27583 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27588 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27603) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27609) ->
                           is_uvar t1
                       | uu____27634 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27668  ->
                          fun uu____27669  ->
                            fun uu____27670  ->
                              match (uu____27668, uu____27669, uu____27670)
                              with
                              | ((a1,uu____27714),(a2,uu____27716),(is_sub_probs,wl2))
                                  ->
                                  let uu____27749 = is_uvar a1  in
                                  if uu____27749
                                  then
                                    ((let uu____27759 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27759
                                      then
                                        let uu____27764 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27766 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27764 uu____27766
                                      else ());
                                     (let uu____27771 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27771 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27569 with
                   | (is_sub_probs,wl2) ->
                       let uu____27799 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27799 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27807 =
                              let uu____27812 =
                                let uu____27813 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27813
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27812
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27807 with
                             | (uu____27820,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27831 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27833 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27831 s uu____27833
                                    in
                                 let uu____27836 =
                                   let uu____27865 =
                                     let uu____27866 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27866.FStar_Syntax_Syntax.n  in
                                   match uu____27865 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27926 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27926 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____27989 =
                                              let uu____28008 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____28008
                                                (fun uu____28112  ->
                                                   match uu____28112 with
                                                   | (l1,l2) ->
                                                       let uu____28185 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____28185))
                                               in
                                            (match uu____27989 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____28290 ->
                                       let uu____28291 =
                                         let uu____28297 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____28297)
                                          in
                                       FStar_Errors.raise_error uu____28291 r
                                    in
                                 (match uu____27836 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____28373 =
                                        let uu____28380 =
                                          let uu____28381 =
                                            let uu____28382 =
                                              let uu____28389 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____28389,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____28382
                                             in
                                          [uu____28381]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____28380
                                          (fun b  ->
                                             let uu____28405 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____28407 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28409 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____28405 uu____28407
                                               uu____28409) r
                                         in
                                      (match uu____28373 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____28419 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____28419
                                             then
                                               let uu____28424 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____28433 =
                                                          let uu____28435 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____28435
                                                           in
                                                        Prims.op_Hat s
                                                          uu____28433) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____28424
                                             else ());
                                            (let wl4 =
                                               let uu___3704_28443 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3704_28443.attempting);
                                                 wl_deferred =
                                                   (uu___3704_28443.wl_deferred);
                                                 wl_deferred_to_tac =
                                                   (uu___3704_28443.wl_deferred_to_tac);
                                                 ctr = (uu___3704_28443.ctr);
                                                 defer_ok =
                                                   (uu___3704_28443.defer_ok);
                                                 smt_ok =
                                                   (uu___3704_28443.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3704_28443.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3704_28443.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits);
                                                 repr_subcomp_allowed =
                                                   (uu___3704_28443.repr_subcomp_allowed)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____28468 =
                                                        let uu____28475 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____28475, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____28468) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____28492 =
                                               let f_sort_is =
                                                 let uu____28502 =
                                                   let uu____28503 =
                                                     let uu____28506 =
                                                       let uu____28507 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28507.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28506
                                                      in
                                                   uu____28503.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28502 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28518,uu____28519::is)
                                                     ->
                                                     let uu____28561 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28561
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28594 ->
                                                     let uu____28595 =
                                                       let uu____28601 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28601)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28595 r
                                                  in
                                               let uu____28607 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28642  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28642
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28663 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28663
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28607
                                                in
                                             match uu____28492 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28688 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28688
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28689 =
                                                   let g_sort_is =
                                                     let uu____28699 =
                                                       let uu____28700 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28700.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28699 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28705,uu____28706::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28766 ->
                                                         let uu____28767 =
                                                           let uu____28773 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28773)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28767 r
                                                      in
                                                   let uu____28779 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28814  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28814
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28835
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28835
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28779
                                                    in
                                                 (match uu____28689 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28862 =
                                                          let uu____28867 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28868 =
                                                            let uu____28869 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28869
                                                             in
                                                          (uu____28867,
                                                            uu____28868)
                                                           in
                                                        match uu____28862
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28897 =
                                                          let uu____28900 =
                                                            let uu____28903 =
                                                              let uu____28906
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28906
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28903
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28900
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28897
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28930 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28930
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
                                                        let uu____28941 =
                                                          let uu____28944 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28947 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28947)
                                                            uu____28944
                                                           in
                                                        solve_prob orig
                                                          uu____28941 [] wl6
                                                         in
                                                      let uu____28948 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28948))))))))))
           in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env  in
           let lift_c1 uu____28976 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____28978 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ
                      in
                   [uu____28978]
               | x -> x  in
             let c12 =
               let uu___3772_28981 = c11  in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3772_28981.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3772_28981.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3772_28981.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3772_28981.FStar_Syntax_Syntax.flags)
               }  in
             let uu____28982 =
               let uu____28987 =
                 FStar_All.pipe_right
                   (let uu___3775_28989 = c12  in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3775_28989.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3775_28989.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3775_28989.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3775_28989.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____28987
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____28982
               (fun uu____29003  ->
                  match uu____29003 with
                  | (c,g) ->
                      let uu____29010 =
                        let uu____29012 = FStar_TypeChecker_Env.is_trivial g
                           in
                        Prims.op_Negation uu____29012  in
                      if uu____29010
                      then
                        let uu____29015 =
                          let uu____29021 =
                            let uu____29023 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name
                               in
                            let uu____29025 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name
                               in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____29023 uu____29025
                             in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____29021)
                           in
                        FStar_Errors.raise_error uu____29015 r
                      else FStar_Syntax_Util.comp_to_comp_typ c)
              in
           let uu____29031 =
             FStar_TypeChecker_Env.is_layered_effect env
               c21.FStar_Syntax_Syntax.effect_name
              in
           if uu____29031
           then solve_layered_sub c11 edge c21
           else
             (let uu____29036 =
                ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                   (let uu____29039 =
                      FStar_Ident.lid_equals
                        c11.FStar_Syntax_Syntax.effect_name
                        c21.FStar_Syntax_Syntax.effect_name
                       in
                    Prims.op_Negation uu____29039))
                  &&
                  (FStar_TypeChecker_Env.is_reifiable_effect env
                     c21.FStar_Syntax_Syntax.effect_name)
                 in
              if uu____29036
              then
                let uu____29042 =
                  mklstr
                    (fun uu____29049  ->
                       let uu____29050 =
                         FStar_Ident.string_of_lid
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____29052 =
                         FStar_Ident.string_of_lid
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Cannot lift from %s to %s, it needs a lift\n"
                         uu____29050 uu____29052)
                   in
                giveup env uu____29042 orig
              else
                (let is_null_wp_2 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___29_29063  ->
                           match uu___29_29063 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | FStar_Syntax_Syntax.MLEFFECT  -> true
                           | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                           | uu____29068 -> false))
                    in
                 let uu____29070 =
                   match ((c11.FStar_Syntax_Syntax.effect_args),
                           (c21.FStar_Syntax_Syntax.effect_args))
                   with
                   | ((wp1,uu____29100)::uu____29101,(wp2,uu____29103)::uu____29104)
                       -> (wp1, wp2)
                   | uu____29177 ->
                       let uu____29202 =
                         let uu____29208 =
                           let uu____29210 =
                             FStar_Syntax_Print.lid_to_string
                               c11.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____29212 =
                             FStar_Syntax_Print.lid_to_string
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Got effects %s and %s, expected normalized effects"
                             uu____29210 uu____29212
                            in
                         (FStar_Errors.Fatal_ExpectNormalizedEffect,
                           uu____29208)
                          in
                       FStar_Errors.raise_error uu____29202
                         env.FStar_TypeChecker_Env.range
                    in
                 match uu____29070 with
                 | (wpc1,wpc2) ->
                     let uu____29222 = FStar_Util.physical_equality wpc1 wpc2
                        in
                     if uu____29222
                     then
                       let uu____29225 =
                         problem_using_guard orig
                           c11.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29225 wl
                     else
                       (let uu____29229 =
                          let uu____29236 =
                            FStar_TypeChecker_Env.effect_decl_opt env
                              c21.FStar_Syntax_Syntax.effect_name
                             in
                          FStar_Util.must uu____29236  in
                        match uu____29229 with
                        | (c2_decl,qualifiers) ->
                            let uu____29257 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____29257
                            then
                              let c1_repr =
                                let uu____29264 =
                                  let uu____29265 =
                                    let uu____29266 = lift_c1 ()  in
                                    FStar_Syntax_Syntax.mk_Comp uu____29266
                                     in
                                  let uu____29267 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____29265 uu____29267
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.4"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____29264
                                 in
                              let c2_repr =
                                let uu____29270 =
                                  let uu____29271 =
                                    FStar_Syntax_Syntax.mk_Comp c21  in
                                  let uu____29272 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____29271 uu____29272
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.5"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____29270
                                 in
                              let uu____29274 =
                                let uu____29279 =
                                  let uu____29281 =
                                    FStar_Syntax_Print.term_to_string c1_repr
                                     in
                                  let uu____29283 =
                                    FStar_Syntax_Print.term_to_string c2_repr
                                     in
                                  FStar_Util.format2
                                    "sub effect repr: %s <: %s" uu____29281
                                    uu____29283
                                   in
                                sub_prob wl c1_repr
                                  problem.FStar_TypeChecker_Common.relation
                                  c2_repr uu____29279
                                 in
                              (match uu____29274 with
                               | (prob,wl1) ->
                                   let wl2 =
                                     solve_prob orig
                                       (FStar_Pervasives_Native.Some
                                          (p_guard prob)) [] wl1
                                      in
                                   let uu____29289 = attempt [prob] wl2  in
                                   solve env uu____29289)
                            else
                              (let g =
                                 if env.FStar_TypeChecker_Env.lax
                                 then FStar_Syntax_Util.t_true
                                 else
                                   (let wpc1_2 =
                                      let uu____29309 = lift_c1 ()  in
                                      FStar_All.pipe_right uu____29309
                                        (fun ct  ->
                                           FStar_List.hd
                                             ct.FStar_Syntax_Syntax.effect_args)
                                       in
                                    if is_null_wp_2
                                    then
                                      ((let uu____29332 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other "Rel")
                                           in
                                        if uu____29332
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
                                          let uu____29342 =
                                            FStar_All.pipe_right c2_decl
                                              FStar_Syntax_Util.get_wp_trivial_combinator
                                             in
                                          match uu____29342 with
                                          | FStar_Pervasives_Native.None  ->
                                              failwith
                                                "Rel doesn't yet handle undefined trivial combinator in an effect"
                                          | FStar_Pervasives_Native.Some t ->
                                              t
                                           in
                                        let uu____29349 =
                                          let uu____29350 =
                                            let uu____29367 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____29370 =
                                              let uu____29381 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____29381; wpc1_2]  in
                                            (uu____29367, uu____29370)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____29350
                                           in
                                        FStar_Syntax_Syntax.mk uu____29349 r))
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
                                       let uu____29430 =
                                         let uu____29431 =
                                           let uu____29448 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____29451 =
                                             let uu____29462 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____29471 =
                                               let uu____29482 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____29482; wpc1_2]  in
                                             uu____29462 :: uu____29471  in
                                           (uu____29448, uu____29451)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____29431
                                          in
                                       FStar_Syntax_Syntax.mk uu____29430 r))
                                  in
                               (let uu____29536 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____29536
                                then
                                  let uu____29541 =
                                    let uu____29543 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Eager_unfolding;
                                        FStar_TypeChecker_Env.Primops;
                                        FStar_TypeChecker_Env.Simplify] env g
                                       in
                                    FStar_Syntax_Print.term_to_string
                                      uu____29543
                                     in
                                  FStar_Util.print1
                                    "WP guard (simplifed) is (%s)\n"
                                    uu____29541
                                else ());
                               (let uu____29547 =
                                  sub_prob wl
                                    c11.FStar_Syntax_Syntax.result_typ
                                    problem.FStar_TypeChecker_Common.relation
                                    c21.FStar_Syntax_Syntax.result_typ
                                    "result type"
                                   in
                                match uu____29547 with
                                | (base_prob,wl1) ->
                                    let wl2 =
                                      let uu____29556 =
                                        let uu____29559 =
                                          FStar_Syntax_Util.mk_conj
                                            (p_guard base_prob) g
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____29562  ->
                                             FStar_Pervasives_Native.Some
                                               uu____29562) uu____29559
                                         in
                                      solve_prob orig uu____29556 [] wl1  in
                                    let uu____29563 = attempt [base_prob] wl2
                                       in
                                    solve env uu____29563))))))
           in
        let uu____29564 = FStar_Util.physical_equality c1 c2  in
        if uu____29564
        then
          let uu____29567 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29567
        else
          ((let uu____29571 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29571
            then
              let uu____29576 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29578 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29576
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29578
            else ());
           (let uu____29583 =
              let uu____29592 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29595 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29592, uu____29595)  in
            match uu____29583 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29613),FStar_Syntax_Syntax.Total
                    (t2,uu____29615)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29632 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29632 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29634,FStar_Syntax_Syntax.Total uu____29635) ->
                     let uu____29652 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29652 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29656),FStar_Syntax_Syntax.Total
                    (t2,uu____29658)) ->
                     let uu____29675 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29675 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29678),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29680)) ->
                     let uu____29697 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29697 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29700),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29702)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29719 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29719 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29722),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29724)) ->
                     let uu____29741 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29741 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29744,FStar_Syntax_Syntax.Comp uu____29745) ->
                     let uu____29754 =
                       let uu___3900_29757 = problem  in
                       let uu____29760 =
                         let uu____29761 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29761
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3900_29757.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29760;
                         FStar_TypeChecker_Common.relation =
                           (uu___3900_29757.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3900_29757.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3900_29757.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3900_29757.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3900_29757.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3900_29757.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3900_29757.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3900_29757.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29754 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29762,FStar_Syntax_Syntax.Comp uu____29763) ->
                     let uu____29772 =
                       let uu___3900_29775 = problem  in
                       let uu____29778 =
                         let uu____29779 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29779
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3900_29775.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29778;
                         FStar_TypeChecker_Common.relation =
                           (uu___3900_29775.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3900_29775.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3900_29775.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3900_29775.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3900_29775.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3900_29775.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3900_29775.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3900_29775.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29772 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29780,FStar_Syntax_Syntax.GTotal uu____29781) ->
                     let uu____29790 =
                       let uu___3912_29793 = problem  in
                       let uu____29796 =
                         let uu____29797 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29797
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3912_29793.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3912_29793.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3912_29793.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29796;
                         FStar_TypeChecker_Common.element =
                           (uu___3912_29793.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3912_29793.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3912_29793.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3912_29793.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3912_29793.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3912_29793.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29790 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29798,FStar_Syntax_Syntax.Total uu____29799) ->
                     let uu____29808 =
                       let uu___3912_29811 = problem  in
                       let uu____29814 =
                         let uu____29815 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29815
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3912_29811.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3912_29811.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3912_29811.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29814;
                         FStar_TypeChecker_Common.element =
                           (uu___3912_29811.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3912_29811.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3912_29811.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3912_29811.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3912_29811.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3912_29811.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29808 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29816,FStar_Syntax_Syntax.Comp uu____29817) ->
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
                               FStar_TypeChecker_Common.SUB))
                        in
                     if uu____29818
                     then
                       let uu____29821 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29821 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29828 =
                            let uu____29833 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29833
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29842 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29843 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29842, uu____29843))
                             in
                          match uu____29828 with
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
                           (let uu____29851 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29851
                            then
                              let uu____29856 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29858 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29856 uu____29858
                            else ());
                           (let uu____29863 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29863 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29866 =
                                  mklstr
                                    (fun uu____29873  ->
                                       let uu____29874 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29876 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29874 uu____29876)
                                   in
                                giveup env uu____29866 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29887 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29887 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29937 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29937 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29962 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29993  ->
                match uu____29993 with
                | (u1,u2) ->
                    let uu____30001 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____30003 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____30001 uu____30003))
         in
      FStar_All.pipe_right uu____29962 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____30040,[])) when
          let uu____30067 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____30067 -> "{}"
      | uu____30070 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____30097 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____30097
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry defs =
            let uu____30128 =
              FStar_List.map
                (fun uu____30142  ->
                   match uu____30142 with
                   | (msg,x) ->
                       let uu____30153 =
                         let uu____30155 = prob_to_string env x  in
                         Prims.op_Hat ": " uu____30155  in
                       Prims.op_Hat msg uu____30153) defs
               in
            FStar_All.pipe_right uu____30128 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30165 = carry g.FStar_TypeChecker_Common.deferred  in
          let uu____30167 = carry g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____30169 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30165 uu____30167 uu____30169 imps
  
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
                  let uu____30226 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30226
                  then
                    let uu____30234 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30236 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30234
                      (rel_to_string rel) uu____30236
                  else "TOP"  in
                let uu____30242 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30242 with
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
              let uu____30302 =
                let uu____30305 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____30308  ->
                     FStar_Pervasives_Native.Some uu____30308) uu____30305
                 in
              FStar_Syntax_Syntax.new_bv uu____30302 t1  in
            let uu____30309 =
              let uu____30314 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30314
               in
            match uu____30309 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____30386 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30386
         then
           let uu____30391 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30391
         else ());
        (let uu____30398 =
           FStar_Util.record_time (fun uu____30405  -> solve env probs)  in
         match uu____30398 with
         | (sol,ms) ->
             ((let uu____30419 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30419
               then
                 let uu____30424 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30424
               else ());
              (match sol with
               | Success (deferred,defer_to_tac,implicits) ->
                   let uu____30440 =
                     FStar_Util.record_time
                       (fun uu____30447  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30440 with
                    | ((),ms1) ->
                        ((let uu____30460 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30460
                          then
                            let uu____30465 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30465
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d,s) ->
                   ((let uu____30479 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30479
                     then
                       let uu____30486 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30486
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
          ((let uu____30514 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30514
            then
              let uu____30519 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30519
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30527 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30527
             then
               let uu____30532 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30532
             else ());
            (let f2 =
               let uu____30538 =
                 let uu____30539 = FStar_Syntax_Util.unmeta f1  in
                 uu____30539.FStar_Syntax_Syntax.n  in
               match uu____30538 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30543 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4031_30544 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4031_30544.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4031_30544.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4031_30544.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4031_30544.FStar_TypeChecker_Common.implicits)
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
            let uu____30596 =
              let uu____30597 =
                let uu____30598 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30599  ->
                       FStar_TypeChecker_Common.NonTrivial uu____30599)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30598;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30597  in
            FStar_All.pipe_left
              (fun uu____30606  -> FStar_Pervasives_Native.Some uu____30606)
              uu____30596
  
let with_guard_no_simp :
  'uuuuuu30616 .
    'uuuuuu30616 ->
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
            let uu____30665 =
              let uu____30666 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30667  ->
                     FStar_TypeChecker_Common.NonTrivial uu____30667)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30666;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30665
  
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
          (let uu____30700 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30700
           then
             let uu____30705 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30707 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30705
               uu____30707
           else ());
          (let uu____30712 =
             let uu____30717 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30717
              in
           match uu____30712 with
           | (prob,wl) ->
               let g =
                 let uu____30725 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30735  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30725  in
               ((let uu____30757 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30757
                 then
                   let uu____30762 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30762
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
        let uu____30783 = try_teq true env t1 t2  in
        match uu____30783 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30788 = FStar_TypeChecker_Env.get_range env  in
              let uu____30789 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30788 uu____30789);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30797 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30797
              then
                let uu____30802 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30804 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30806 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30802
                  uu____30804 uu____30806
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
        (let uu____30830 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30830
         then
           let uu____30835 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30837 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30835
             uu____30837
         else ());
        (let uu____30842 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30842 with
         | (prob,x,wl) ->
             let g =
               let uu____30857 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30868  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30857  in
             ((let uu____30890 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30890
               then
                 let uu____30895 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30895
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30903 =
                     let uu____30904 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30904 g1  in
                   FStar_Pervasives_Native.Some uu____30903)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30926 = FStar_TypeChecker_Env.get_range env  in
          let uu____30927 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30926 uu____30927
  
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
        (let uu____30956 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30956
         then
           let uu____30961 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30963 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30961 uu____30963
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30974 =
           let uu____30981 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30981 "sub_comp"
            in
         match uu____30974 with
         | (prob,wl) ->
             let wl1 =
               let uu___4104_30992 = wl  in
               {
                 attempting = (uu___4104_30992.attempting);
                 wl_deferred = (uu___4104_30992.wl_deferred);
                 wl_deferred_to_tac = (uu___4104_30992.wl_deferred_to_tac);
                 ctr = (uu___4104_30992.ctr);
                 defer_ok = (uu___4104_30992.defer_ok);
                 smt_ok = (uu___4104_30992.smt_ok);
                 umax_heuristic_ok = (uu___4104_30992.umax_heuristic_ok);
                 tcenv = (uu___4104_30992.tcenv);
                 wl_implicits = (uu___4104_30992.wl_implicits);
                 repr_subcomp_allowed = true
               }  in
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30997 =
                 FStar_Util.record_time
                   (fun uu____31009  ->
                      let uu____31010 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____31021  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____31010)
                  in
               match uu____30997 with
               | (r,ms) ->
                   ((let uu____31053 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____31053
                     then
                       let uu____31058 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____31060 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____31062 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____31058 uu____31060
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____31062
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
      fun uu____31100  ->
        match uu____31100 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31143 =
                 let uu____31149 =
                   let uu____31151 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31153 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31151 uu____31153
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31149)  in
               let uu____31157 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31143 uu____31157)
               in
            let equiv v v' =
              let uu____31170 =
                let uu____31175 = FStar_Syntax_Subst.compress_univ v  in
                let uu____31176 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31175, uu____31176)  in
              match uu____31170 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31200 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____31231 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____31231 with
                      | FStar_Syntax_Syntax.U_unif uu____31238 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31269  ->
                                    match uu____31269 with
                                    | (u,v') ->
                                        let uu____31278 = equiv v v'  in
                                        if uu____31278
                                        then
                                          let uu____31283 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____31283 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____31304 -> []))
               in
            let uu____31309 =
              let wl =
                let uu___4147_31313 = empty_worklist env  in
                {
                  attempting = (uu___4147_31313.attempting);
                  wl_deferred = (uu___4147_31313.wl_deferred);
                  wl_deferred_to_tac = (uu___4147_31313.wl_deferred_to_tac);
                  ctr = (uu___4147_31313.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4147_31313.smt_ok);
                  umax_heuristic_ok = (uu___4147_31313.umax_heuristic_ok);
                  tcenv = (uu___4147_31313.tcenv);
                  wl_implicits = (uu___4147_31313.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4147_31313.repr_subcomp_allowed)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31332  ->
                      match uu____31332 with
                      | (lb,v) ->
                          let uu____31339 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____31339 with
                           | USolved wl1 -> ()
                           | uu____31342 -> fail lb v)))
               in
            let rec check_ineq uu____31353 =
              match uu____31353 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31365) -> true
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
                      uu____31393,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31395,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31408) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____31416,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____31425 -> false)
               in
            let uu____31431 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31448  ->
                      match uu____31448 with
                      | (u,v) ->
                          let uu____31456 = check_ineq (u, v)  in
                          if uu____31456
                          then true
                          else
                            ((let uu____31464 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31464
                              then
                                let uu____31469 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31471 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____31469
                                  uu____31471
                              else ());
                             false)))
               in
            if uu____31431
            then ()
            else
              ((let uu____31481 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31481
                then
                  ((let uu____31487 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31487);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31499 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31499))
                else ());
               (let uu____31512 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31512))
  
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
          let fail uu____31594 =
            match uu____31594 with
            | (d,s) ->
                let msg = explain env d s  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d)
             in
          let wl =
            let uu___4225_31621 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
            {
              attempting = (uu___4225_31621.attempting);
              wl_deferred = (uu___4225_31621.wl_deferred);
              wl_deferred_to_tac = (uu___4225_31621.wl_deferred_to_tac);
              ctr = (uu___4225_31621.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4225_31621.umax_heuristic_ok);
              tcenv = (uu___4225_31621.tcenv);
              wl_implicits = (uu___4225_31621.wl_implicits);
              repr_subcomp_allowed = (uu___4225_31621.repr_subcomp_allowed)
            }  in
          (let uu____31624 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____31624
           then
             let uu____31629 = FStar_Util.string_of_bool defer_ok  in
             let uu____31631 = wl_to_string wl  in
             let uu____31633 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits)
                in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31629 uu____31631 uu____31633
           else ());
          (let g1 =
             let uu____31639 = solve_and_commit env wl fail  in
             match uu____31639 with
             | FStar_Pervasives_Native.Some
                 (uu____31648::uu____31649,uu____31650,uu____31651) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred,defer_to_tac,imps) ->
                 let uu___4242_31685 = g  in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4242_31685.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4242_31685.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31691 ->
                 failwith "Impossible: should have raised a failure already"
              in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let uu___4247_31702 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4247_31702.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4247_31702.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4247_31702.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs = ([], []);
              FStar_TypeChecker_Common.implicits =
                (uu___4247_31702.FStar_TypeChecker_Common.implicits)
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
          (let uu____31798 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____31798
           then
             let uu____31803 = guard_to_string env g  in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31803
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g  in
           let ret_g =
             let uu___4264_31810 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4264_31810.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4264_31810.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4264_31810.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4264_31810.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31811 =
             let uu____31813 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31813  in
           if uu____31811
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____31825 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31826 =
                        let uu____31828 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31828
                         in
                      FStar_Errors.diag uu____31825 uu____31826)
                   else ();
                   (let vc1 =
                      let uu____31834 =
                        let uu____31838 =
                          let uu____31840 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31840  in
                        FStar_Pervasives_Native.Some uu____31838  in
                      FStar_Profiling.profile
                        (fun uu____31843  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31834 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug
                    then
                      (let uu____31847 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31848 =
                         let uu____31850 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31850
                          in
                       FStar_Errors.diag uu____31847 uu____31848)
                    else ();
                    (let uu____31856 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31856 "discharge_guard'" env vc1);
                    (let uu____31858 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31858 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____31867 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31868 =
                                 let uu____31870 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31870
                                  in
                               FStar_Errors.diag uu____31867 uu____31868)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____31880 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31881 =
                                 let uu____31883 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31883
                                  in
                               FStar_Errors.diag uu____31880 uu____31881)
                            else ();
                            (let vcs =
                               let uu____31897 = FStar_Options.use_tactics ()
                                  in
                               if uu____31897
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31919  ->
                                      (let uu____31921 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left
                                         (fun uu____31923  -> ()) uu____31921);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31966  ->
                                               match uu____31966 with
                                               | (env1,goal,opts) ->
                                                   let uu____31982 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____31982, opts)))))
                               else
                                 (let uu____31986 =
                                    let uu____31993 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____31993)  in
                                  [uu____31986])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____32026  ->
                                     match uu____32026 with
                                     | (env1,goal,opts) ->
                                         let uu____32036 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____32036 with
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
                                                 (let uu____32047 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____32048 =
                                                    let uu____32050 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____32052 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____32050 uu____32052
                                                     in
                                                  FStar_Errors.diag
                                                    uu____32047 uu____32048)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____32059 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____32060 =
                                                    let uu____32062 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____32062
                                                     in
                                                  FStar_Errors.diag
                                                    uu____32059 uu____32060)
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
      let uu____32080 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____32080 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____32089 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____32089
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____32103 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____32103 with
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
        let uu____32133 = try_teq false env t1 t2  in
        match uu____32133 with
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
        let uu____32176 =
          ((imp.FStar_TypeChecker_Common.imp_uvar),
            (imp.FStar_TypeChecker_Common.imp_range))
           in
        match uu____32176 with
        | (ctx_u,r) ->
            let t_norm =
              FStar_TypeChecker_Normalize.normalize
                FStar_TypeChecker_Normalize.whnf_steps env
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            let uu____32186 =
              let uu____32187 = FStar_Syntax_Subst.compress t_norm  in
              uu____32187.FStar_Syntax_Syntax.n  in
            (match uu____32186 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid
                 ->
                 let uu____32193 =
                   FStar_All.pipe_right r
                     FStar_Syntax_Syntax.unit_const_with_range
                    in
                 FStar_All.pipe_right uu____32193
                   (fun uu____32196  ->
                      FStar_Pervasives_Native.Some uu____32196)
             | FStar_Syntax_Syntax.Tm_refine (b,uu____32198) when
                 FStar_Syntax_Util.is_unit b.FStar_Syntax_Syntax.sort ->
                 let uu____32203 =
                   FStar_All.pipe_right r
                     FStar_Syntax_Syntax.unit_const_with_range
                    in
                 FStar_All.pipe_right uu____32203
                   (fun uu____32206  ->
                      FStar_Pervasives_Native.Some uu____32206)
             | uu____32207 -> FStar_Pervasives_Native.None)
         in
      let tx = FStar_Syntax_Unionfind.new_transaction ()  in
      let b =
        FStar_List.fold_left
          (fun b  ->
             fun imp  ->
               let uu____32220 = imp_value imp  in
               match uu____32220 with
               | FStar_Pervasives_Native.Some tm ->
                   (commit
                      [TERM ((imp.FStar_TypeChecker_Common.imp_uvar), tm)];
                    true)
               | FStar_Pervasives_Native.None  -> b) false imps
         in
      FStar_Syntax_Unionfind.commit tx; (imps, b)
  
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
            let uu____32262 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32262 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32269 ->
                     let uu____32270 =
                       let uu____32271 = FStar_Syntax_Subst.compress r  in
                       uu____32271.FStar_Syntax_Syntax.n  in
                     (match uu____32270 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32276) ->
                          unresolved ctx_u'
                      | uu____32293 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32317 = acc  in
            match uu____32317 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then
                       let uu____32328 =
                         try_solve_single_valued_implicits env out  in
                       (match uu____32328 with
                        | (out1,changed1) ->
                            if changed1
                            then until_fixpoint ([], false) out1
                            else out1)
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____32351 = hd  in
                     (match uu____32351 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____32362 = unresolved ctx_u  in
                             if uu____32362
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32373 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32373
                                     then
                                       let uu____32377 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32377
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32386 = teq_nosmt env1 t tm
                                          in
                                       match uu____32386 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4405_32396 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4405_32396.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4405_32396.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4405_32396.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4405_32396.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4405_32396.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4405_32396.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4405_32396.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4408_32398 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4408_32398.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4408_32398.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4408_32398.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl)))
                               | uu____32401 ->
                                   until_fixpoint ((hd :: out), changed) tl
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl
                               else
                                 (let env1 =
                                    let uu___4413_32413 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4413_32413.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4413_32413.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4413_32413.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4413_32413.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4413_32413.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4413_32413.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4413_32413.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4413_32413.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4413_32413.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4413_32413.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4413_32413.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4413_32413.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4413_32413.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4413_32413.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4413_32413.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4413_32413.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4413_32413.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4413_32413.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4413_32413.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4413_32413.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4413_32413.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4413_32413.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4413_32413.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4413_32413.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4413_32413.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4413_32413.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4413_32413.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4413_32413.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4413_32413.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4413_32413.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4413_32413.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4413_32413.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4413_32413.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4413_32413.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4413_32413.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4413_32413.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4413_32413.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4413_32413.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4413_32413.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4413_32413.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4413_32413.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4413_32413.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4413_32413.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4413_32413.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4413_32413.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___4413_32413.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4418_32418 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4418_32418.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4418_32418.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4418_32418.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4418_32418.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4418_32418.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4418_32418.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4418_32418.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4418_32418.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4418_32418.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4418_32418.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4418_32418.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4418_32418.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4418_32418.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4418_32418.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4418_32418.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4418_32418.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4418_32418.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4418_32418.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4418_32418.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4418_32418.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4418_32418.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4418_32418.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4418_32418.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4418_32418.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4418_32418.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4418_32418.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4418_32418.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4418_32418.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4418_32418.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4418_32418.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4418_32418.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4418_32418.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4418_32418.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4418_32418.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4418_32418.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4418_32418.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4418_32418.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4418_32418.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4418_32418.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4418_32418.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4418_32418.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4418_32418.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4418_32418.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4418_32418.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4418_32418.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4418_32418.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      }
                                    else env1  in
                                  (let uu____32423 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32423
                                   then
                                     let uu____32428 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32430 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32432 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32434 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32428 uu____32430 uu____32432
                                       reason uu____32434
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4424_32441  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32448 =
                                             let uu____32458 =
                                               let uu____32466 =
                                                 let uu____32468 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32470 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32472 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32468 uu____32470
                                                   uu____32472
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32466, r)
                                                in
                                             [uu____32458]  in
                                           FStar_Errors.add_errors
                                             uu____32448);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32491 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32502  ->
                                               let uu____32503 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32505 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32507 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32503 uu____32505
                                                 reason uu____32507)) env2 g1
                                         true
                                        in
                                     match uu____32491 with
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
          let uu___4436_32515 = g  in
          let uu____32516 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4436_32515.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4436_32515.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4436_32515.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4436_32515.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32516
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____32531 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32531
       then
         let uu____32536 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32536
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
      (let uu____32567 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32567
       then
         let uu____32572 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32572
       else ());
      (let g1 = solve_deferred_constraints env g  in
       let g2 =
         FStar_TypeChecker_DeferredImplicits.solve_deferred_to_tactic_goals
           env g1
          in
       (let uu____32580 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ResolveImplicitsHook")
           in
        if uu____32580
        then
          let uu____32585 = guard_to_string env g2  in
          FStar_Util.print1
            "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
            uu____32585
        else ());
       (let g3 = resolve_implicits env g2  in
        match g3.FStar_TypeChecker_Common.implicits with
        | [] ->
            let uu____32591 = discharge_guard env g3  in
            FStar_All.pipe_left (fun uu____32592  -> ()) uu____32591
        | imp::uu____32594 ->
            let uu____32597 =
              let uu____32603 =
                let uu____32605 =
                  FStar_Syntax_Print.uvar_to_string
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                   in
                let uu____32607 =
                  FStar_TypeChecker_Normalize.term_to_string env
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                   in
                FStar_Util.format3
                  "Failed to resolve implicit argument %s of type %s introduced for %s"
                  uu____32605 uu____32607
                  imp.FStar_TypeChecker_Common.imp_reason
                 in
              (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32603)
               in
            FStar_Errors.raise_error uu____32597
              imp.FStar_TypeChecker_Common.imp_range))
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32627 = teq env t1 t2  in
        force_trivial_guard env uu____32627
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32646 = teq_nosmt env t1 t2  in
        match uu____32646 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4469_32665 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4469_32665.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4469_32665.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4469_32665.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4469_32665.FStar_TypeChecker_Common.implicits)
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
        (let uu____32701 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32701
         then
           let uu____32706 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32708 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32706
             uu____32708
         else ());
        (let uu____32713 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32713 with
         | (prob,x,wl) ->
             let g =
               let uu____32732 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32743  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32732  in
             ((let uu____32765 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____32765
               then
                 let uu____32770 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____32772 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____32774 =
                   let uu____32776 = FStar_Util.must g  in
                   guard_to_string env uu____32776  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32770 uu____32772 uu____32774
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
        let uu____32813 = check_subtyping env t1 t2  in
        match uu____32813 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32832 =
              let uu____32833 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32833 g  in
            FStar_Pervasives_Native.Some uu____32832
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32852 = check_subtyping env t1 t2  in
        match uu____32852 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32871 =
              let uu____32872 =
                let uu____32873 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32873]  in
              FStar_TypeChecker_Env.close_guard env uu____32872 g  in
            FStar_Pervasives_Native.Some uu____32871
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32911 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32911
         then
           let uu____32916 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32918 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32916
             uu____32918
         else ());
        (let uu____32923 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32923 with
         | (prob,x,wl) ->
             let g =
               let uu____32938 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32949  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32938  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32974 =
                      let uu____32975 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32975]  in
                    FStar_TypeChecker_Env.close_guard env uu____32974 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33016 = subtype_nosmt env t1 t2  in
        match uu____33016 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  