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
                     ((let uu___93_1016 = wl  in
                       {
                         attempting = (uu___93_1016.attempting);
                         wl_deferred = (uu___93_1016.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___93_1016.wl_deferred_to_tac);
                         ctr = (uu___93_1016.ctr);
                         defer_ok = (uu___93_1016.defer_ok);
                         smt_ok = (uu___93_1016.smt_ok);
                         umax_heuristic_ok = (uu___93_1016.umax_heuristic_ok);
                         tcenv = (uu___93_1016.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits));
                         repr_subcomp_allowed =
                           (uu___93_1016.repr_subcomp_allowed)
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
            let uu___99_1049 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___99_1049.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___99_1049.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___99_1049.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___99_1049.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___99_1049.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___99_1049.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___99_1049.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___99_1049.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___99_1049.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___99_1049.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___99_1049.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___99_1049.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___99_1049.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___99_1049.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___99_1049.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___99_1049.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___99_1049.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___99_1049.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___99_1049.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___99_1049.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___99_1049.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___99_1049.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___99_1049.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___99_1049.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___99_1049.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___99_1049.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___99_1049.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___99_1049.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___99_1049.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___99_1049.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___99_1049.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___99_1049.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___99_1049.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___99_1049.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___99_1049.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___99_1049.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___99_1049.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___99_1049.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___99_1049.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___99_1049.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___99_1049.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___99_1049.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___99_1049.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___99_1049.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___99_1049.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___99_1049.FStar_TypeChecker_Env.enable_defer_to_tac)
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
        let uu___108_1220 = wl  in
        let uu____1221 =
          let uu____1231 = as_wl_deferred wl defer_to_tac  in
          FStar_List.append wl.wl_deferred_to_tac uu____1231  in
        {
          attempting = (uu___108_1220.attempting);
          wl_deferred = (uu___108_1220.wl_deferred);
          wl_deferred_to_tac = uu____1221;
          ctr = (uu___108_1220.ctr);
          defer_ok = (uu___108_1220.defer_ok);
          smt_ok = (uu___108_1220.smt_ok);
          umax_heuristic_ok = (uu___108_1220.umax_heuristic_ok);
          tcenv = (uu___108_1220.tcenv);
          wl_implicits = (FStar_List.append wl.wl_implicits imps);
          repr_subcomp_allowed = (uu___108_1220.repr_subcomp_allowed)
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
    let uu___168_1705 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___168_1705.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___168_1705.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___168_1705.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___168_1705.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___168_1705.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___168_1705.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___168_1705.FStar_TypeChecker_Common.rank)
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
          (let uu___180_1757 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___180_1757.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___180_1757.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___180_1757.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___180_1757.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___180_1757.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___180_1757.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___180_1757.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___180_1757.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___180_1757.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___184_1765 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___184_1765.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___184_1765.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___184_1765.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___184_1765.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___184_1765.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___184_1765.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___184_1765.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___184_1765.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___184_1765.FStar_TypeChecker_Common.rank)
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
        let uu___277_2290 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___277_2290.wl_deferred);
          wl_deferred_to_tac = (uu___277_2290.wl_deferred_to_tac);
          ctr = (uu___277_2290.ctr);
          defer_ok = (uu___277_2290.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___277_2290.umax_heuristic_ok);
          tcenv = (uu___277_2290.tcenv);
          wl_implicits = (uu___277_2290.wl_implicits);
          repr_subcomp_allowed = (uu___277_2290.repr_subcomp_allowed)
        }
  
let wl_of_guard :
  'uuuuuu2298 .
    FStar_TypeChecker_Env.env ->
      ('uuuuuu2298 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___281_2321 = empty_worklist env  in
      let uu____2322 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____2322;
        wl_deferred = (uu___281_2321.wl_deferred);
        wl_deferred_to_tac = (uu___281_2321.wl_deferred_to_tac);
        ctr = (uu___281_2321.ctr);
        defer_ok = (uu___281_2321.defer_ok);
        smt_ok = (uu___281_2321.smt_ok);
        umax_heuristic_ok = (uu___281_2321.umax_heuristic_ok);
        tcenv = (uu___281_2321.tcenv);
        wl_implicits = (uu___281_2321.wl_implicits);
        repr_subcomp_allowed = (uu___281_2321.repr_subcomp_allowed)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___286_2343 = wl  in
        {
          attempting = (uu___286_2343.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          wl_deferred_to_tac = (uu___286_2343.wl_deferred_to_tac);
          ctr = (uu___286_2343.ctr);
          defer_ok = (uu___286_2343.defer_ok);
          smt_ok = (uu___286_2343.smt_ok);
          umax_heuristic_ok = (uu___286_2343.umax_heuristic_ok);
          tcenv = (uu___286_2343.tcenv);
          wl_implicits = (uu___286_2343.wl_implicits);
          repr_subcomp_allowed = (uu___286_2343.repr_subcomp_allowed)
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
  
let (should_defer_uvar_to_user_tac :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun env  ->
    fun u  ->
      if Prims.op_Negation env.FStar_TypeChecker_Env.enable_defer_to_tac
      then false
      else
        (let uu____2422 = find_user_tac_for_uvar env u  in
         FStar_Option.isSome uu____2422)
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___305_2442 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___305_2442.wl_deferred);
         wl_deferred_to_tac = (uu___305_2442.wl_deferred_to_tac);
         ctr = (uu___305_2442.ctr);
         defer_ok = (uu___305_2442.defer_ok);
         smt_ok = (uu___305_2442.smt_ok);
         umax_heuristic_ok = (uu___305_2442.umax_heuristic_ok);
         tcenv = (uu___305_2442.tcenv);
         wl_implicits = (uu___305_2442.wl_implicits);
         repr_subcomp_allowed = (uu___305_2442.repr_subcomp_allowed)
       })
  
let mk_eq2 :
  'uuuuuu2456 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2456 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____2490 = FStar_Syntax_Util.type_u ()  in
            match uu____2490 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____2502 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____2502 with
                 | (uu____2514,tt,wl1) ->
                     let uu____2517 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2517, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2523  ->
    match uu___14_2523 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun uu____2529  -> FStar_TypeChecker_Common.TProb uu____2529)
          (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun uu____2535  -> FStar_TypeChecker_Common.CProb uu____2535)
          (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2543 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2543 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2563  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'uuuuuu2605 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'uuuuuu2605 ->
            FStar_TypeChecker_Common.rel ->
              'uuuuuu2605 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('uuuuuu2605 FStar_TypeChecker_Common.problem * worklist)
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
                        let uu____2692 =
                          let uu____2701 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2701]  in
                        FStar_List.append scope uu____2692
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2744 =
                      let uu____2747 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2747  in
                    FStar_List.append uu____2744
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2766 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2766 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2786 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2786;
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
                  (let uu____2860 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2860 with
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
                  (let uu____2948 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2948 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'uuuuuu2986 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'uuuuuu2986 ->
          FStar_TypeChecker_Common.rel ->
            'uuuuuu2986 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('uuuuuu2986 FStar_TypeChecker_Common.problem * worklist)
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
                          let uu____3054 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____3054]  in
                        let uu____3073 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____3073
                     in
                  let uu____3076 =
                    let uu____3083 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___388_3094 = wl  in
                       {
                         attempting = (uu___388_3094.attempting);
                         wl_deferred = (uu___388_3094.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___388_3094.wl_deferred_to_tac);
                         ctr = (uu___388_3094.ctr);
                         defer_ok = (uu___388_3094.defer_ok);
                         smt_ok = (uu___388_3094.smt_ok);
                         umax_heuristic_ok =
                           (uu___388_3094.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___388_3094.wl_implicits);
                         repr_subcomp_allowed =
                           (uu___388_3094.repr_subcomp_allowed)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____3083
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____3076 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____3106 =
                              let uu____3107 =
                                let uu____3116 =
                                  FStar_Syntax_Syntax.bv_to_name x  in
                                FStar_All.pipe_left
                                  FStar_Syntax_Syntax.as_arg uu____3116
                                 in
                              [uu____3107]  in
                            FStar_Syntax_Syntax.mk_Tm_app lg uu____3106 loc
                         in
                      let prob =
                        let uu____3144 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____3144;
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
                let uu____3192 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____3192;
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
  'uuuuuu3207 .
    worklist ->
      'uuuuuu3207 FStar_TypeChecker_Common.problem ->
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
              let uu____3240 =
                let uu____3243 =
                  let uu____3244 =
                    let uu____3251 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____3251)  in
                  FStar_Syntax_Syntax.NT uu____3244  in
                [uu____3243]  in
              FStar_Syntax_Subst.subst uu____3240 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____3273 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____3273
        then
          let uu____3281 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____3284 = prob_to_string env d  in
          let uu____3286 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____3293 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3281 uu____3284 uu____3286 uu____3293
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____3305 -> failwith "impossible"  in
           let uu____3308 =
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
           match uu____3308 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3351  ->
            match uu___15_3351 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3365 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____3369 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3369 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_3400  ->
           match uu___16_3400 with
           | UNIV uu____3403 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____3410 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____3410
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
        (fun uu___17_3438  ->
           match uu___17_3438 with
           | UNIV (u',t) ->
               let uu____3443 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____3443
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3450 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3462 =
        let uu____3463 =
          let uu____3464 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3464
           in
        FStar_Syntax_Subst.compress uu____3463  in
      FStar_All.pipe_right uu____3462 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3476 =
        let uu____3477 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3477  in
      FStar_All.pipe_right uu____3476 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3489 =
        let uu____3493 =
          let uu____3495 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3495  in
        FStar_Pervasives_Native.Some uu____3493  in
      FStar_Profiling.profile (fun uu____3498  -> sn' env t) uu____3489
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
          let uu____3523 =
            let uu____3527 =
              let uu____3529 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3529  in
            FStar_Pervasives_Native.Some uu____3527  in
          FStar_Profiling.profile
            (fun uu____3532  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3523
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3540 = FStar_Syntax_Util.head_and_args t  in
    match uu____3540 with
    | (h,uu____3559) ->
        let uu____3584 =
          let uu____3585 = FStar_Syntax_Subst.compress h  in
          uu____3585.FStar_Syntax_Syntax.n  in
        (match uu____3584 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3590 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3603 =
        let uu____3607 =
          let uu____3609 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3609  in
        FStar_Pervasives_Native.Some uu____3607  in
      FStar_Profiling.profile
        (fun uu____3614  ->
           let uu____3615 = should_strongly_reduce t  in
           if uu____3615
           then
             let uu____3618 =
               let uu____3619 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3619  in
             FStar_All.pipe_right uu____3618 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3603 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'uuuuuu3630 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'uuuuuu3630) ->
        (FStar_Syntax_Syntax.term * 'uuuuuu3630)
  =
  fun env  ->
    fun t  ->
      let uu____3653 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3653, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3705  ->
              match uu____3705 with
              | (x,imp) ->
                  let uu____3724 =
                    let uu___494_3725 = x  in
                    let uu____3726 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___494_3725.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___494_3725.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3726
                    }  in
                  (uu____3724, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3750 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3750
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3754 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3754
        | uu____3757 -> u2  in
      let uu____3758 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3758
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3775 =
          let uu____3779 =
            let uu____3781 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3781  in
          FStar_Pervasives_Native.Some uu____3779  in
        FStar_Profiling.profile
          (fun uu____3784  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3775 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3906 = norm_refinement env t12  in
                 match uu____3906 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3921;
                     FStar_Syntax_Syntax.vars = uu____3922;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3946 =
                       let uu____3948 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3950 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3948 uu____3950
                        in
                     failwith uu____3946)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3966 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm uu____3966
          | FStar_Syntax_Syntax.Tm_uinst uu____3967 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4004 =
                   let uu____4005 = FStar_Syntax_Subst.compress t1'  in
                   uu____4005.FStar_Syntax_Syntax.n  in
                 match uu____4004 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4020 -> aux true t1'
                 | uu____4028 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____4043 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4074 =
                   let uu____4075 = FStar_Syntax_Subst.compress t1'  in
                   uu____4075.FStar_Syntax_Syntax.n  in
                 match uu____4074 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4090 -> aux true t1'
                 | uu____4098 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4113 ->
              if norm
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4160 =
                   let uu____4161 = FStar_Syntax_Subst.compress t1'  in
                   uu____4161.FStar_Syntax_Syntax.n  in
                 match uu____4160 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4176 -> aux true t1'
                 | uu____4184 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____4199 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____4214 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____4229 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____4244 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____4259 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____4288 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____4321 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____4342 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____4369 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____4397 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____4434 ->
              let uu____4441 =
                let uu____4443 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4445 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4443 uu____4445
                 in
              failwith uu____4441
          | FStar_Syntax_Syntax.Tm_ascribed uu____4460 ->
              let uu____4487 =
                let uu____4489 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4491 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4489 uu____4491
                 in
              failwith uu____4487
          | FStar_Syntax_Syntax.Tm_delayed uu____4506 ->
              let uu____4521 =
                let uu____4523 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4525 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4523 uu____4525
                 in
              failwith uu____4521
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4540 =
                let uu____4542 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4544 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4542 uu____4544
                 in
              failwith uu____4540
           in
        let uu____4559 = whnf env t1  in aux false uu____4559
  
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
      let uu____4604 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4604 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4645 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4645, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta  ->
    fun env  ->
      fun t  ->
        let uu____4672 = base_and_refinement_maybe_delta delta env t  in
        match uu____4672 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4732  ->
    match uu____4732 with
    | (t_base,refopt) ->
        let uu____4763 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4763 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4805 =
      let uu____4809 =
        let uu____4812 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4837  ->
                  match uu____4837 with | (uu____4845,uu____4846,x) -> x))
           in
        FStar_List.append wl.attempting uu____4812  in
      FStar_List.map (wl_prob_to_string wl) uu____4809  in
    FStar_All.pipe_right uu____4805 (FStar_String.concat "\n\t")
  
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
  fun uu____4906  ->
    match uu____4906 with
    | Flex (uu____4908,u,uu____4910) -> u.FStar_Syntax_Syntax.ctx_uvar_reason
  
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4917  ->
    match uu____4917 with
    | Flex (uu____4919,c,args) ->
        let uu____4922 = print_ctx_uvar c  in
        let uu____4924 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4922 uu____4924
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4934 = FStar_Syntax_Util.head_and_args t  in
    match uu____4934 with
    | (head,_args) ->
        let uu____4978 =
          let uu____4979 = FStar_Syntax_Subst.compress head  in
          uu____4979.FStar_Syntax_Syntax.n  in
        (match uu____4978 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4983 -> true
         | uu____4997 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____5005 = FStar_Syntax_Util.head_and_args t  in
    match uu____5005 with
    | (head,_args) ->
        let uu____5048 =
          let uu____5049 = FStar_Syntax_Subst.compress head  in
          uu____5049.FStar_Syntax_Syntax.n  in
        (match uu____5048 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____5053) -> u
         | uu____5070 -> failwith "Not a flex-uvar")
  
let (ensure_no_uvar_subst :
  FStar_Syntax_Syntax.term ->
    worklist -> (FStar_Syntax_Syntax.term * worklist))
  =
  fun t0  ->
    fun wl  ->
      let bv_not_affected_by s x =
        let t_x = FStar_Syntax_Syntax.bv_to_name x  in
        let t_x' = FStar_Syntax_Subst.subst' s t_x  in
        let uu____5106 =
          let uu____5107 = FStar_Syntax_Subst.compress t_x'  in
          uu____5107.FStar_Syntax_Syntax.n  in
        match uu____5106 with
        | FStar_Syntax_Syntax.Tm_name y -> FStar_Syntax_Syntax.bv_eq x y
        | uu____5112 -> false  in
      let binding_not_affected_by s b =
        match b with
        | FStar_Syntax_Syntax.Binding_var x -> bv_not_affected_by s x
        | uu____5128 -> true  in
      let uu____5130 = FStar_Syntax_Util.head_and_args t0  in
      match uu____5130 with
      | (head,args) ->
          let uu____5177 =
            let uu____5178 = FStar_Syntax_Subst.compress head  in
            uu____5178.FStar_Syntax_Syntax.n  in
          (match uu____5177 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____5186)) -> (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,uu____5202) when
               FStar_List.isEmpty uv.FStar_Syntax_Syntax.ctx_uvar_binders ->
               (t0, wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____5243 =
                 FStar_Common.max_suffix (binding_not_affected_by s)
                   uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                  in
               (match uu____5243 with
                | (gamma_aff,new_gamma) ->
                    (match gamma_aff with
                     | [] -> (t0, wl)
                     | uu____5270 ->
                         let dom_binders =
                           FStar_TypeChecker_Env.binders_of_bindings
                             gamma_aff
                            in
                         let uu____5274 =
                           let uu____5281 =
                             FStar_TypeChecker_Env.binders_of_bindings
                               new_gamma
                              in
                           let uu____5290 =
                             let uu____5293 =
                               FStar_Syntax_Syntax.mk_Total
                                 uv.FStar_Syntax_Syntax.ctx_uvar_typ
                                in
                             FStar_Syntax_Util.arrow dom_binders uu____5293
                              in
                           new_uvar
                             (Prims.op_Hat
                                uv.FStar_Syntax_Syntax.ctx_uvar_reason
                                "; force delayed") wl
                             t0.FStar_Syntax_Syntax.pos new_gamma uu____5281
                             uu____5290
                             uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                             uv.FStar_Syntax_Syntax.ctx_uvar_meta
                            in
                         (match uu____5274 with
                          | (v,t_v,wl1) ->
                              let args_sol =
                                FStar_List.map
                                  (fun uu____5329  ->
                                     match uu____5329 with
                                     | (x,i) ->
                                         let uu____5348 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         (uu____5348, i)) dom_binders
                                 in
                              let sol =
                                FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                                  t0.FStar_Syntax_Syntax.pos
                                 in
                              (FStar_Syntax_Util.set_uvar
                                 uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                               (let args_sol_s =
                                  FStar_List.map
                                    (fun uu____5378  ->
                                       match uu____5378 with
                                       | (a,i) ->
                                           let uu____5397 =
                                             FStar_Syntax_Subst.subst' s a
                                              in
                                           (uu____5397, i)) args_sol
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk_Tm_app t_v
                                    (FStar_List.append args_sol_s args)
                                    t0.FStar_Syntax_Syntax.pos
                                   in
                                (t, wl1))))))
           | uu____5407 ->
               failwith "ensure_no_uvar_subst: expected a uvar at the head")
  
let (destruct_flex_t' : FStar_Syntax_Syntax.term -> flex_t) =
  fun t  ->
    let uu____5419 = FStar_Syntax_Util.head_and_args t  in
    match uu____5419 with
    | (head,args) ->
        let uu____5462 =
          let uu____5463 = FStar_Syntax_Subst.compress head  in
          uu____5463.FStar_Syntax_Syntax.n  in
        (match uu____5462 with
         | FStar_Syntax_Syntax.Tm_uvar (uv,s) -> Flex (t, uv, args)
         | uu____5484 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term -> worklist -> (flex_t * worklist)) =
  fun t  ->
    fun wl  ->
      let uu____5505 = ensure_no_uvar_subst t wl  in
      match uu____5505 with
      | (t1,wl1) ->
          let uu____5516 = destruct_flex_t' t1  in (uu____5516, wl1)
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5533 =
          let uu____5556 =
            let uu____5557 = FStar_Syntax_Subst.compress k  in
            uu____5557.FStar_Syntax_Syntax.n  in
          match uu____5556 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5639 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5639)
              else
                (let uu____5674 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5674 with
                 | (ys',t1,uu____5707) ->
                     let uu____5712 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5712))
          | uu____5751 ->
              let uu____5752 =
                let uu____5757 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5757)  in
              ((ys, t), uu____5752)
           in
        match uu____5533 with
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
                 let uu____5852 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5852 c  in
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
               (let uu____5930 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5930
                then
                  let uu____5935 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5937 = print_ctx_uvar uv  in
                  let uu____5939 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5935 uu____5937 uu____5939
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5948 =
                   let uu____5950 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5950  in
                 let uu____5953 =
                   let uu____5956 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5956
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5948 uu____5953 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail uu____5989 =
               let uu____5990 =
                 let uu____5992 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5994 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5992 uu____5994
                  in
               failwith uu____5990  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____6060  ->
                       match uu____6060 with
                       | (a,i) ->
                           let uu____6081 =
                             let uu____6082 = FStar_Syntax_Subst.compress a
                                in
                             uu____6082.FStar_Syntax_Syntax.n  in
                           (match uu____6081 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____6108 -> (fail (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____6118 =
                 let uu____6120 = is_flex g  in Prims.op_Negation uu____6120
                  in
               if uu____6118
               then (if resolve_ok then wl else (fail (); wl))
               else
                 (let uu____6129 = destruct_flex_t g wl  in
                  match uu____6129 with
                  | (Flex (uu____6134,uv1,args),wl1) ->
                      ((let uu____6139 = args_as_binders args  in
                        assign_solution uu____6139 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___772_6141 = wl1  in
              {
                attempting = (uu___772_6141.attempting);
                wl_deferred = (uu___772_6141.wl_deferred);
                wl_deferred_to_tac = (uu___772_6141.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___772_6141.defer_ok);
                smt_ok = (uu___772_6141.smt_ok);
                umax_heuristic_ok = (uu___772_6141.umax_heuristic_ok);
                tcenv = (uu___772_6141.tcenv);
                wl_implicits = (uu___772_6141.wl_implicits);
                repr_subcomp_allowed = (uu___772_6141.repr_subcomp_allowed)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____6166 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____6166
         then
           let uu____6171 = FStar_Util.string_of_int pid  in
           let uu____6173 = uvis_to_string wl.tcenv sol  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6171 uu____6173
         else ());
        commit sol;
        (let uu___780_6179 = wl  in
         {
           attempting = (uu___780_6179.attempting);
           wl_deferred = (uu___780_6179.wl_deferred);
           wl_deferred_to_tac = (uu___780_6179.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___780_6179.defer_ok);
           smt_ok = (uu___780_6179.smt_ok);
           umax_heuristic_ok = (uu___780_6179.umax_heuristic_ok);
           tcenv = (uu___780_6179.tcenv);
           wl_implicits = (uu___780_6179.wl_implicits);
           repr_subcomp_allowed = (uu___780_6179.repr_subcomp_allowed)
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
          (let uu____6215 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____6215
           then
             let uu____6220 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____6224 = uvis_to_string wl.tcenv uvis  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6220 uu____6224
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
        let uu____6251 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____6251 FStar_Util.set_elements  in
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
      let uu____6291 = occurs uk t  in
      match uu____6291 with
      | (uvars,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6330 =
                 let uu____6332 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____6334 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6332 uu____6334
                  in
               FStar_Pervasives_Native.Some uu____6330)
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
          let uu____6445 = FStar_Syntax_Syntax.bv_eq b b'  in
          if uu____6445
          then
            let uu____6456 = maximal_prefix bs_tail bs'_tail  in
            (match uu____6456 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6507 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6564  ->
             match uu____6564 with
             | (x,uu____6576) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6594 = FStar_List.last bs  in
      match uu____6594 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6618) ->
          let uu____6629 =
            FStar_Util.prefix_until
              (fun uu___18_6644  ->
                 match uu___18_6644 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6647 -> false) g
             in
          (match uu____6629 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6661,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6698 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6698 with
        | (pfx,uu____6708) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6720 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6720 with
             | (uu____6728,src',wl1) ->
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
                 | uu____6842 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6843 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6907  ->
                  fun uu____6908  ->
                    match (uu____6907, uu____6908) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____7011 =
                          let uu____7013 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____7013
                           in
                        if uu____7011
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____7047 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____7047
                           then
                             let uu____7064 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____7064)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6843 with | (isect,uu____7114) -> FStar_List.rev isect
  
let binders_eq :
  'uuuuuu7150 'uuuuuu7151 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu7150) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7151) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7209  ->
              fun uu____7210  ->
                match (uu____7209, uu____7210) with
                | ((a,uu____7229),(b,uu____7231)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'uuuuuu7247 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7247) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____7278  ->
           match uu____7278 with
           | (y,uu____7285) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'uuuuuu7295 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu7295) Prims.list ->
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
                   let uu____7457 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____7457
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7490 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7542 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7586 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7607 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___19_7615  ->
    match uu___19_7615 with
    | MisMatch (d1,d2) ->
        let uu____7627 =
          let uu____7629 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7631 =
            let uu____7633 =
              let uu____7635 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7635 ")"  in
            Prims.op_Hat ") (" uu____7633  in
          Prims.op_Hat uu____7629 uu____7631  in
        Prims.op_Hat "MisMatch (" uu____7627
    | HeadMatch u ->
        let uu____7642 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7642
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___20_7651  ->
    match uu___20_7651 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7668 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          let uu____7683 =
            (let uu____7689 =
               FStar_Ident.string_of_lid env.FStar_TypeChecker_Env.curmodule
                in
             let uu____7691 =
               FStar_Ident.nsstr
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             uu____7689 = uu____7691) &&
              (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
             in
          if uu____7683 then d1 else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7700 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7700 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7711 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7735 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7745 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7764 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7764
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7765 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7766 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7767 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7780 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7794 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7818) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7824,uu____7825) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7867) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7892;
             FStar_Syntax_Syntax.index = uu____7893;
             FStar_Syntax_Syntax.sort = t2;_},uu____7895)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7903 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7904 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7905 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7920 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7927 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7947 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7947
  
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
           { FStar_Syntax_Syntax.blob = uu____7966;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7967;
             FStar_Syntax_Syntax.ltyp = uu____7968;
             FStar_Syntax_Syntax.rng = uu____7969;_},uu____7970)
            ->
            let uu____7981 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7981 t21
        | (uu____7982,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7983;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7984;
             FStar_Syntax_Syntax.ltyp = uu____7985;
             FStar_Syntax_Syntax.rng = uu____7986;_})
            ->
            let uu____7997 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7997
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            let uu____8000 = FStar_Syntax_Syntax.bv_eq x y  in
            if uu____8000
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____8011 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____8011
            then FullMatch
            else
              (let uu____8016 =
                 let uu____8025 =
                   let uu____8028 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____8028  in
                 let uu____8029 =
                   let uu____8032 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____8032  in
                 (uu____8025, uu____8029)  in
               MisMatch uu____8016)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____8038),FStar_Syntax_Syntax.Tm_uinst (g,uu____8040)) ->
            let uu____8049 = head_matches env f g  in
            FStar_All.pipe_right uu____8049 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____8050) -> HeadMatch true
        | (uu____8052,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____8056 = FStar_Const.eq_const c d  in
            if uu____8056
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____8066),FStar_Syntax_Syntax.Tm_uvar (uv',uu____8068)) ->
            let uu____8101 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____8101
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____8111),FStar_Syntax_Syntax.Tm_refine (y,uu____8113)) ->
            let uu____8122 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8122 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____8124),uu____8125) ->
            let uu____8130 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____8130 head_match
        | (uu____8131,FStar_Syntax_Syntax.Tm_refine (x,uu____8133)) ->
            let uu____8138 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8138 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8139,FStar_Syntax_Syntax.Tm_type
           uu____8140) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____8142,FStar_Syntax_Syntax.Tm_arrow uu____8143) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head,uu____8174),FStar_Syntax_Syntax.Tm_app (head',uu____8176))
            ->
            let uu____8225 = head_matches env head head'  in
            FStar_All.pipe_right uu____8225 head_match
        | (FStar_Syntax_Syntax.Tm_app (head,uu____8227),uu____8228) ->
            let uu____8253 = head_matches env head t21  in
            FStar_All.pipe_right uu____8253 head_match
        | (uu____8254,FStar_Syntax_Syntax.Tm_app (head,uu____8256)) ->
            let uu____8281 = head_matches env t11 head  in
            FStar_All.pipe_right uu____8281 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8282,FStar_Syntax_Syntax.Tm_let
           uu____8283) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____8311,FStar_Syntax_Syntax.Tm_match uu____8312) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8358,FStar_Syntax_Syntax.Tm_abs
           uu____8359) -> HeadMatch true
        | uu____8397 ->
            let uu____8402 =
              let uu____8411 = delta_depth_of_term env t11  in
              let uu____8414 = delta_depth_of_term env t21  in
              (uu____8411, uu____8414)  in
            MisMatch uu____8402
  
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
              let uu____8483 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8483  in
            (let uu____8485 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8485
             then
               let uu____8490 = FStar_Syntax_Print.term_to_string t  in
               let uu____8492 = FStar_Syntax_Print.term_to_string head  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8490 uu____8492
             else ());
            (let uu____8497 =
               let uu____8498 = FStar_Syntax_Util.un_uinst head  in
               uu____8498.FStar_Syntax_Syntax.n  in
             match uu____8497 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8504 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8504 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8518 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8518
                        then
                          let uu____8523 =
                            FStar_Syntax_Print.term_to_string head  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8523
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8528 ->
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
                      let uu____8546 =
                        let uu____8548 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8548 = FStar_Syntax_Util.Equal  in
                      if uu____8546
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8555 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8555
                          then
                            let uu____8560 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8562 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8560
                              uu____8562
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8567 -> FStar_Pervasives_Native.None)
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
            (let uu____8719 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8719
             then
               let uu____8724 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8726 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8728 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8724
                 uu____8726 uu____8728
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8756 =
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
               match uu____8756 with
               | (t12,t22) -> aux retry (n_delta + Prims.int_one) t12 t22  in
             let reduce_both_and_try_again d r1 =
               let uu____8804 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8804 with
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
                  uu____8842),uu____8843)
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8864 =
                      let uu____8873 = maybe_inline t11  in
                      let uu____8876 = maybe_inline t21  in
                      (uu____8873, uu____8876)  in
                    match uu____8864 with
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
                 (uu____8919,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8920))
                 ->
                 if Prims.op_Negation retry
                 then fail n_delta r t11 t21
                 else
                   (let uu____8941 =
                      let uu____8950 = maybe_inline t11  in
                      let uu____8953 = maybe_inline t21  in
                      (uu____8950, uu____8953)  in
                    match uu____8941 with
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
             | MisMatch uu____9008 -> fail n_delta r t11 t21
             | uu____9017 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____9032 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____9032
           then
             let uu____9037 = FStar_Syntax_Print.term_to_string t1  in
             let uu____9039 = FStar_Syntax_Print.term_to_string t2  in
             let uu____9041 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____9049 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____9066 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____9066
                    (fun uu____9101  ->
                       match uu____9101 with
                       | (t11,t21) ->
                           let uu____9109 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____9111 =
                             let uu____9113 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____9113  in
                           Prims.op_Hat uu____9109 uu____9111))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____9037 uu____9039 uu____9041 uu____9049
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____9130 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____9130 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___21_9145  ->
    match uu___21_9145 with
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
      let uu___1269_9194 = p  in
      let uu____9197 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____9198 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1269_9194.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9197;
        FStar_TypeChecker_Common.relation =
          (uu___1269_9194.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9198;
        FStar_TypeChecker_Common.element =
          (uu___1269_9194.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1269_9194.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1269_9194.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1269_9194.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1269_9194.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1269_9194.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9213 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____9213
            (fun uu____9218  -> FStar_TypeChecker_Common.TProb uu____9218)
      | FStar_TypeChecker_Common.CProb uu____9219 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____9242 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____9242 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9250 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9250 with
           | (lh,lhs_args) ->
               let uu____9297 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9297 with
                | (rh,rhs_args) ->
                    let uu____9344 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9357,FStar_Syntax_Syntax.Tm_uvar uu____9358)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9447 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9474,uu____9475)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9490,FStar_Syntax_Syntax.Tm_uvar uu____9491)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9506,FStar_Syntax_Syntax.Tm_arrow uu____9507)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1320_9537 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1320_9537.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1320_9537.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1320_9537.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1320_9537.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1320_9537.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1320_9537.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1320_9537.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1320_9537.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1320_9537.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9540,FStar_Syntax_Syntax.Tm_type uu____9541)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1320_9557 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1320_9557.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1320_9557.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1320_9557.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1320_9557.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1320_9557.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1320_9557.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1320_9557.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1320_9557.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1320_9557.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9560,FStar_Syntax_Syntax.Tm_uvar uu____9561)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1320_9577 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1320_9577.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1320_9577.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1320_9577.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1320_9577.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1320_9577.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1320_9577.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1320_9577.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1320_9577.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1320_9577.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9580,FStar_Syntax_Syntax.Tm_uvar uu____9581)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9596,uu____9597)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9612,FStar_Syntax_Syntax.Tm_uvar uu____9613)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9628,uu____9629) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9344 with
                     | (rank,tp1) ->
                         let uu____9642 =
                           FStar_All.pipe_right
                             (let uu___1340_9646 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1340_9646.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1340_9646.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1340_9646.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1340_9646.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1340_9646.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1340_9646.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1340_9646.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1340_9646.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1340_9646.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun uu____9649  ->
                                FStar_TypeChecker_Common.TProb uu____9649)
                            in
                         (rank, uu____9642))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9653 =
            FStar_All.pipe_right
              (let uu___1344_9657 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1344_9657.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1344_9657.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1344_9657.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1344_9657.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1344_9657.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1344_9657.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1344_9657.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1344_9657.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1344_9657.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               })
              (fun uu____9660  -> FStar_TypeChecker_Common.CProb uu____9660)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9653)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9720 probs =
      match uu____9720 with
      | (min_rank,min,out) ->
          (match probs with
           | [] ->
               (match (min, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9801 -> FStar_Pervasives_Native.None)
           | hd::tl ->
               let uu____9822 = rank wl.tcenv hd  in
               (match uu____9822 with
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
                      (let uu____9883 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9888 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9888)
                          in
                       if uu____9883
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
          let uu____9961 = FStar_Syntax_Util.head_and_args t  in
          match uu____9961 with
          | (hd,uu____9980) ->
              let uu____10005 =
                let uu____10006 = FStar_Syntax_Subst.compress hd  in
                uu____10006.FStar_Syntax_Syntax.n  in
              (match uu____10005 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____10011) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____10046  ->
                           match uu____10046 with
                           | (y,uu____10055) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____10078  ->
                                       match uu____10078 with
                                       | (x,uu____10087) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____10092 -> false)
           in
        let uu____10094 = rank tcenv p  in
        match uu____10094 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____10103 -> true
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
    match projectee with | UDeferred _0 -> true | uu____10184 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____10203 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____10222 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____10239 = FStar_Thunk.mkv s  in UFailed uu____10239 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____10254 = mklstr s  in UFailed uu____10254 
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
                        let uu____10305 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____10305 with
                        | (k,uu____10313) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10328 -> false)))
            | uu____10330 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10382 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  FStar_Syntax_Util.eq_univs uv1 uv2))
                           in
                        if uu____10382 then uv1 :: uvs else uvs) [])
               in
            let filter =
              FStar_List.filter
                (fun u  ->
                   let uu____10406 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  -> FStar_Syntax_Util.eq_univs u u'))
                      in
                   Prims.op_Negation uu____10406)
               in
            let uu____10413 = filter u12  in
            let uu____10416 = filter u22  in (uu____10413, uu____10416)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10451 = filter_out_common_univs us1 us2  in
                   (match uu____10451 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10511 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10511 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10514 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10531  ->
                               let uu____10532 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10534 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10532 uu____10534))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10560 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10560 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10586 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10586 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10589 ->
                   ufailed_thunk
                     (fun uu____10600  ->
                        let uu____10601 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10603 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10601 uu____10603 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10606,uu____10607) ->
              let uu____10609 =
                let uu____10611 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10613 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10611 uu____10613
                 in
              failwith uu____10609
          | (FStar_Syntax_Syntax.U_unknown ,uu____10616) ->
              let uu____10617 =
                let uu____10619 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10621 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10619 uu____10621
                 in
              failwith uu____10617
          | (uu____10624,FStar_Syntax_Syntax.U_bvar uu____10625) ->
              let uu____10627 =
                let uu____10629 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10631 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10629 uu____10631
                 in
              failwith uu____10627
          | (uu____10634,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10635 =
                let uu____10637 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10639 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10637 uu____10639
                 in
              failwith uu____10635
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              let uu____10644 =
                let uu____10646 = FStar_Ident.string_of_id x  in
                let uu____10648 = FStar_Ident.string_of_id y  in
                uu____10646 = uu____10648  in
              if uu____10644
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10679 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10679
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10698 = occurs_univ v1 u3  in
              if uu____10698
              then
                let uu____10701 =
                  let uu____10703 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10705 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10703 uu____10705
                   in
                try_umax_components u11 u21 uu____10701
              else
                (let uu____10710 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10710)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10724 = occurs_univ v1 u3  in
              if uu____10724
              then
                let uu____10727 =
                  let uu____10729 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10731 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10729 uu____10731
                   in
                try_umax_components u11 u21 uu____10727
              else
                (let uu____10736 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10736)
          | (FStar_Syntax_Syntax.U_max uu____10737,uu____10738) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10746 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10746
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10752,FStar_Syntax_Syntax.U_max uu____10753) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10761 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10761
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10767,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10769,FStar_Syntax_Syntax.U_name uu____10770) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10772) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10774) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10776,FStar_Syntax_Syntax.U_succ uu____10777) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10779,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10886 = bc1  in
      match uu____10886 with
      | (bs1,mk_cod1) ->
          let uu____10930 = bc2  in
          (match uu____10930 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____11041 = aux xs ys  in
                     (match uu____11041 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____11124 =
                       let uu____11131 = mk_cod1 xs  in ([], uu____11131)  in
                     let uu____11134 =
                       let uu____11141 = mk_cod2 ys  in ([], uu____11141)  in
                     (uu____11124, uu____11134)
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
                  let uu____11210 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____11210 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____11213 =
                    let uu____11214 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____11214 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____11213
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____11219 = has_type_guard t1 t2  in (uu____11219, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____11220 = has_type_guard t2 t1  in (uu____11220, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___22_11227  ->
    match uu___22_11227 with
    | Flex (uu____11229,uu____11230,[]) -> true
    | uu____11240 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____11254 = f  in
      match uu____11254 with
      | Flex (uu____11256,u,uu____11258) ->
          should_defer_uvar_to_user_tac wl.tcenv u
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____11282 = f  in
      match uu____11282 with
      | Flex
          (uu____11289,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____11290;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11291;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____11294;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____11295;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____11296;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____11297;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11363  ->
                 match uu____11363 with
                 | (y,uu____11372) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11526 =
                  let uu____11541 =
                    let uu____11544 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11544  in
                  ((FStar_List.rev pat_binders), uu____11541)  in
                FStar_Pervasives_Native.Some uu____11526
            | (uu____11577,[]) ->
                let uu____11608 =
                  let uu____11623 =
                    let uu____11626 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11626  in
                  ((FStar_List.rev pat_binders), uu____11623)  in
                FStar_Pervasives_Native.Some uu____11608
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11717 =
                  let uu____11718 = FStar_Syntax_Subst.compress a  in
                  uu____11718.FStar_Syntax_Syntax.n  in
                (match uu____11717 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11738 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11738
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1681_11768 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1681_11768.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1681_11768.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst =
                          let uu____11772 =
                            let uu____11773 =
                              let uu____11780 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11780)  in
                            FStar_Syntax_Syntax.NT uu____11773  in
                          [uu____11772]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst formals1  in
                        let t_res1 = FStar_Syntax_Subst.subst subst t_res  in
                        aux
                          (((let uu___1687_11796 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1687_11796.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1687_11796.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11797 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11837 =
                  let uu____11844 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11844  in
                (match uu____11837 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11903 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11928 ->
               let uu____11929 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11929 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____12261 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____12261
       then
         let uu____12266 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12266
       else ());
      (let uu____12272 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____12272
       then
         let uu____12277 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12277
       else ());
      (let uu____12282 = next_prob probs  in
       match uu____12282 with
       | FStar_Pervasives_Native.Some (hd,tl,rank1) ->
           let probs1 =
             let uu___1714_12309 = probs  in
             {
               attempting = tl;
               wl_deferred = (uu___1714_12309.wl_deferred);
               wl_deferred_to_tac = (uu___1714_12309.wl_deferred_to_tac);
               ctr = (uu___1714_12309.ctr);
               defer_ok = (uu___1714_12309.defer_ok);
               smt_ok = (uu___1714_12309.smt_ok);
               umax_heuristic_ok = (uu___1714_12309.umax_heuristic_ok);
               tcenv = (uu___1714_12309.tcenv);
               wl_implicits = (uu___1714_12309.wl_implicits);
               repr_subcomp_allowed = (uu___1714_12309.repr_subcomp_allowed)
             }  in
           (def_check_prob "solve,hd" hd;
            (match hd with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12318 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____12318
                 then
                   let uu____12321 =
                     solve_prob hd FStar_Pervasives_Native.None [] probs1  in
                   solve env uu____12321
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
                           (let uu___1726_12333 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1726_12333.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1726_12333.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1726_12333.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1726_12333.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1726_12333.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1726_12333.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1726_12333.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1726_12333.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1726_12333.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12353 =
                  let uu____12360 = as_deferred probs.wl_deferred_to_tac  in
                  ([], uu____12360, (probs.wl_implicits))  in
                Success uu____12353
            | uu____12366 ->
                let uu____12376 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12441  ->
                          match uu____12441 with
                          | (c,uu____12451,uu____12452) -> c < probs.ctr))
                   in
                (match uu____12376 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12500 =
                            let uu____12507 = as_deferred probs.wl_deferred
                               in
                            let uu____12508 =
                              as_deferred probs.wl_deferred_to_tac  in
                            (uu____12507, uu____12508, (probs.wl_implicits))
                             in
                          Success uu____12500
                      | uu____12509 ->
                          let uu____12519 =
                            let uu___1740_12520 = probs  in
                            let uu____12521 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12542  ->
                                      match uu____12542 with
                                      | (uu____12550,uu____12551,y) -> y))
                               in
                            {
                              attempting = uu____12521;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1740_12520.wl_deferred_to_tac);
                              ctr = (uu___1740_12520.ctr);
                              defer_ok = (uu___1740_12520.defer_ok);
                              smt_ok = (uu___1740_12520.smt_ok);
                              umax_heuristic_ok =
                                (uu___1740_12520.umax_heuristic_ok);
                              tcenv = (uu___1740_12520.tcenv);
                              wl_implicits = (uu___1740_12520.wl_implicits);
                              repr_subcomp_allowed =
                                (uu___1740_12520.repr_subcomp_allowed)
                            }  in
                          solve env uu____12519))))

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
            let uu____12560 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12560 with
            | USolved wl1 ->
                let uu____12562 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12562
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12565 = defer_lit "" orig wl1  in
                solve env uu____12565

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
                  let uu____12616 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12616 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12619 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12632;
                  FStar_Syntax_Syntax.vars = uu____12633;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12636;
                  FStar_Syntax_Syntax.vars = uu____12637;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12650,uu____12651) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12659,FStar_Syntax_Syntax.Tm_uinst uu____12660) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12668 -> USolved wl

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
            ((let uu____12679 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12679
              then
                let uu____12684 = prob_to_string env orig  in
                let uu____12686 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12684 uu____12686
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
            let uu___1822_12701 = wl1  in
            let uu____12702 =
              let uu____12712 =
                let uu____12720 = FStar_Thunk.mkv reason  in
                ((wl1.ctr), uu____12720, orig)  in
              uu____12712 :: (wl1.wl_deferred_to_tac)  in
            {
              attempting = (uu___1822_12701.attempting);
              wl_deferred = (uu___1822_12701.wl_deferred);
              wl_deferred_to_tac = uu____12702;
              ctr = (uu___1822_12701.ctr);
              defer_ok = (uu___1822_12701.defer_ok);
              smt_ok = (uu___1822_12701.smt_ok);
              umax_heuristic_ok = (uu___1822_12701.umax_heuristic_ok);
              tcenv = (uu___1822_12701.tcenv);
              wl_implicits = (uu___1822_12701.wl_implicits);
              repr_subcomp_allowed = (uu___1822_12701.repr_subcomp_allowed)
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
                let uu____12749 = FStar_Syntax_Util.head_and_args t  in
                match uu____12749 with
                | (head,uu____12773) ->
                    let uu____12798 =
                      let uu____12799 = FStar_Syntax_Subst.compress head  in
                      uu____12799.FStar_Syntax_Syntax.n  in
                    (match uu____12798 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12809) ->
                         let uu____12826 =
                           should_defer_uvar_to_user_tac wl.tcenv uv  in
                         (uu____12826,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12830 -> (false, ""))
                 in
              let uu____12835 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs  in
              (match uu____12835 with
               | (l1,r1) ->
                   let uu____12848 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs  in
                   (match uu____12848 with
                    | (l2,r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12865 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl
                              in
                           solve env uu____12865)))
          | uu____12866 ->
              let uu____12867 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl  in
              solve env uu____12867

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
               let uu____12953 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12953 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____13008 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____13008
                then
                  let uu____13013 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____13015 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____13013 uu____13015
                else ());
               (let uu____13020 = head_matches_delta env1 wl2 t1 t2  in
                match uu____13020 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____13066 = eq_prob t1 t2 wl2  in
                         (match uu____13066 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____13087 ->
                         let uu____13096 = eq_prob t1 t2 wl2  in
                         (match uu____13096 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13146 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13161 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13162 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13161, uu____13162)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13167 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13168 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13167, uu____13168)
                            in
                         (match uu____13146 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13199 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13199 with
                                | (t1_hd,t1_args) ->
                                    let uu____13244 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13244 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13310 =
                                              let uu____13317 =
                                                let uu____13328 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____13328 :: t1_args  in
                                              let uu____13345 =
                                                let uu____13354 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____13354 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____13403  ->
                                                   fun uu____13404  ->
                                                     fun uu____13405  ->
                                                       match (uu____13403,
                                                               uu____13404,
                                                               uu____13405)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____13455),
                                                          (a2,uu____13457))
                                                           ->
                                                           let uu____13494 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13494
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13317
                                                uu____13345
                                               in
                                            match uu____13310 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1925_13520 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1925_13520.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1925_13520.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1925_13520.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1925_13520.tcenv);
                                                    wl_implicits = [];
                                                    repr_subcomp_allowed =
                                                      (uu___1925_13520.repr_subcomp_allowed)
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13531 =
                                                  solve env1 wl'  in
                                                (match uu____13531 with
                                                 | Success
                                                     (uu____13534,defer_to_tac,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13538 =
                                                         extend_wl wl4
                                                           defer_to_tac imps
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13538))
                                                 | Failed uu____13539 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13571 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13571 with
                                | (t1_base,p1_opt) ->
                                    let uu____13607 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13607 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine x t =
                                             let uu____13706 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13706
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
                                               let uu____13759 =
                                                 op phi11 phi21  in
                                               refine x1 uu____13759
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
                                               let uu____13791 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13791
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
                                               let uu____13823 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine x1 uu____13823
                                           | uu____13826 -> t_base  in
                                         let uu____13843 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13843 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13857 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13857, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13864 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13864 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13900 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13900 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13936 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13936
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
                              let uu____13960 = combine t11 t21 wl2  in
                              (match uu____13960 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13993 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13993
                                     then
                                       let uu____13998 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13998
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____14040 ts1 =
               match uu____14040 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____14103 = pairwise out t wl2  in
                        (match uu____14103 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14139 =
               let uu____14150 = FStar_List.hd ts  in (uu____14150, [], wl1)
                in
             let uu____14159 = FStar_List.tl ts  in
             aux uu____14139 uu____14159  in
           let uu____14166 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14166 with
           | (this_flex,this_rigid) ->
               let uu____14192 =
                 let uu____14193 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14193.FStar_Syntax_Syntax.n  in
               (match uu____14192 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14218 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14218
                    then
                      let uu____14221 = destruct_flex_t this_flex wl  in
                      (match uu____14221 with
                       | (flex,wl1) ->
                           let uu____14228 = quasi_pattern env flex  in
                           (match uu____14228 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t1)
                                ->
                                ((let uu____14247 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14247
                                  then
                                    let uu____14252 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14252
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t1
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14259 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2035_14262 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2035_14262.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2035_14262.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2035_14262.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2035_14262.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2035_14262.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2035_14262.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2035_14262.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2035_14262.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2035_14262.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14259)
                | uu____14263 ->
                    ((let uu____14265 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14265
                      then
                        let uu____14270 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14270
                      else ());
                     (let uu____14275 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14275 with
                      | (u,_args) ->
                          let uu____14318 =
                            let uu____14319 = FStar_Syntax_Subst.compress u
                               in
                            uu____14319.FStar_Syntax_Syntax.n  in
                          (match uu____14318 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv t =
                                 let uu____14347 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____14347 with
                                 | (u',uu____14366) ->
                                     let uu____14391 =
                                       let uu____14392 = whnf env u'  in
                                       uu____14392.FStar_Syntax_Syntax.n  in
                                     (match uu____14391 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14414 -> false)
                                  in
                               let uu____14416 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___23_14439  ->
                                         match uu___23_14439 with
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
                                              | uu____14453 -> false)
                                         | uu____14457 -> false))
                                  in
                               (match uu____14416 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14472 = whnf env this_rigid
                                         in
                                      let uu____14473 =
                                        FStar_List.collect
                                          (fun uu___24_14479  ->
                                             match uu___24_14479 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14485 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14485]
                                             | uu____14489 -> [])
                                          bounds_probs
                                         in
                                      uu____14472 :: uu____14473  in
                                    let uu____14490 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14490 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14523 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14538 =
                                               let uu____14539 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14539.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14538 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14551 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14551)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14562 -> bound  in
                                           let uu____14563 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14563)  in
                                         (match uu____14523 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14598 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14598
                                                then
                                                  let wl'1 =
                                                    let uu___2095_14604 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2095_14604.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2095_14604.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2095_14604.ctr);
                                                      defer_ok =
                                                        (uu___2095_14604.defer_ok);
                                                      smt_ok =
                                                        (uu___2095_14604.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2095_14604.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2095_14604.tcenv);
                                                      wl_implicits =
                                                        (uu___2095_14604.wl_implicits);
                                                      repr_subcomp_allowed =
                                                        (uu___2095_14604.repr_subcomp_allowed)
                                                    }  in
                                                  let uu____14605 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14605
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14611 =
                                                  solve_t env eq_prob
                                                    (let uu___2100_14613 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2100_14613.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2100_14613.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2100_14613.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2100_14613.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2100_14613.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2100_14613.tcenv);
                                                       wl_implicits = [];
                                                       repr_subcomp_allowed =
                                                         (uu___2100_14613.repr_subcomp_allowed)
                                                     })
                                                   in
                                                match uu____14611 with
                                                | Success
                                                    (uu____14615,defer_to_tac,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2107_14619 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2107_14619.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2107_14619.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2107_14619.ctr);
                                                        defer_ok =
                                                          (uu___2107_14619.defer_ok);
                                                        smt_ok =
                                                          (uu___2107_14619.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2107_14619.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2107_14619.tcenv);
                                                        wl_implicits =
                                                          (uu___2107_14619.wl_implicits);
                                                        repr_subcomp_allowed
                                                          =
                                                          (uu___2107_14619.repr_subcomp_allowed)
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
                                                    let uu____14636 =
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
                                                    ((let uu____14648 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14648
                                                      then
                                                        let uu____14653 =
                                                          let uu____14655 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14655
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14653
                                                      else ());
                                                     (let uu____14668 =
                                                        let uu____14683 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14683)
                                                         in
                                                      match uu____14668 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14705))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14731 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14731
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
                                                                  let uu____14751
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14751))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14776 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14776
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
                                                                    let uu____14796
                                                                    =
                                                                    let uu____14801
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14801
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14796
                                                                    [] wl2
                                                                     in
                                                                  let uu____14807
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14807))))
                                                      | uu____14808 ->
                                                          let uu____14823 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14823 p)))))))
                           | uu____14830 when flip ->
                               let uu____14831 =
                                 let uu____14833 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14835 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14833 uu____14835
                                  in
                               failwith uu____14831
                           | uu____14838 ->
                               let uu____14839 =
                                 let uu____14841 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14843 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14841 uu____14843
                                  in
                               failwith uu____14839)))))

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
                      (fun uu____14879  ->
                         match uu____14879 with
                         | (x,i) ->
                             let uu____14898 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14898, i)) bs_lhs
                     in
                  let uu____14901 = lhs  in
                  match uu____14901 with
                  | Flex (uu____14902,u_lhs,uu____14904) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____15001 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____15011 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____15011, univ)
                             in
                          match uu____15001 with
                          | (k,univ) ->
                              let uu____15018 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____15018 with
                               | (uu____15035,u,wl3) ->
                                   let uu____15038 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____15038, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____15064 =
                              let uu____15077 =
                                let uu____15088 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____15088 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15139  ->
                                   fun uu____15140  ->
                                     match (uu____15139, uu____15140) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15241 =
                                           let uu____15248 =
                                             let uu____15251 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15251
                                              in
                                           copy_uvar u_lhs [] uu____15248 wl2
                                            in
                                         (match uu____15241 with
                                          | (uu____15280,t_a,wl3) ->
                                              let uu____15283 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____15283 with
                                               | (uu____15302,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____15077
                                ([], wl1)
                               in
                            (match uu____15064 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2220_15358 = ct  in
                                   let uu____15359 =
                                     let uu____15362 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____15362
                                      in
                                   let uu____15377 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2220_15358.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2220_15358.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15359;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15377;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2220_15358.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2223_15395 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2223_15395.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2223_15395.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____15398 =
                        FStar_Syntax_Util.arrow_formals_comp arrow  in
                      (match uu____15398 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15436 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____15436 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15447 =
                                          let uu____15452 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15452)  in
                                        TERM uu____15447  in
                                      let uu____15453 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15453 with
                                       | (sub_prob,wl3) ->
                                           let uu____15467 =
                                             let uu____15468 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15468
                                              in
                                           solve env uu____15467))
                             | (x,imp)::formals2 ->
                                 let uu____15490 =
                                   let uu____15497 =
                                     let uu____15500 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15500
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15497 wl1
                                    in
                                 (match uu____15490 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15521 =
                                          let uu____15524 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15524
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15521 u_x
                                         in
                                      let uu____15525 =
                                        let uu____15528 =
                                          let uu____15531 =
                                            let uu____15532 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15532, imp)  in
                                          [uu____15531]  in
                                        FStar_List.append bs_terms
                                          uu____15528
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15525 formals2 wl2)
                              in
                           let uu____15559 = occurs_check u_lhs arrow  in
                           (match uu____15559 with
                            | (uu____15572,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15588 =
                                    mklstr
                                      (fun uu____15593  ->
                                         let uu____15594 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15594)
                                     in
                                  giveup_or_defer env orig wl uu____15588
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
              (let uu____15627 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15627
               then
                 let uu____15632 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15635 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15632 (rel_to_string (p_rel orig)) uu____15635
               else ());
              (let rec aux wl1 scope env1 subst xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15766 = rhs wl1 scope env1 subst  in
                     (match uu____15766 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15789 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15789
                            then
                              let uu____15794 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15794
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15872 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15872 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2293_15874 = hd1  in
                       let uu____15875 =
                         FStar_Syntax_Subst.subst subst
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2293_15874.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2293_15874.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15875
                       }  in
                     let hd21 =
                       let uu___2296_15879 = hd2  in
                       let uu____15880 =
                         FStar_Syntax_Subst.subst subst
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2296_15879.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2296_15879.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15880
                       }  in
                     let uu____15883 =
                       let uu____15888 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15888
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15883 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst1 =
                            let uu____15911 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15911
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15918 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst1 xs1 ys1
                             in
                          (match uu____15918 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15990 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15990
                                  in
                               ((let uu____16008 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____16008
                                 then
                                   let uu____16013 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____16015 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____16013
                                     uu____16015
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail -> fail))
                 | uu____16050 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____16086 = aux wl [] env [] bs1 bs2  in
               match uu____16086 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16145 = attempt sub_probs wl2  in
                   solve env1 uu____16145)

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
            let uu___2334_16165 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2334_16165.wl_deferred_to_tac);
              ctr = (uu___2334_16165.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2334_16165.tcenv);
              wl_implicits = [];
              repr_subcomp_allowed = (uu___2334_16165.repr_subcomp_allowed)
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16177 = try_solve env wl'  in
          match uu____16177 with
          | Success (uu____16178,defer_to_tac,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps  in solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16191 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16191 wl)

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
            let uu____16197 = should_defer_flex_to_user_tac wl lhs  in
            if uu____16197
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16210 =
                   FStar_List.map FStar_Pervasives_Native.fst bs  in
                 FStar_Util.as_set uu____16210 FStar_Syntax_Syntax.order_bv
                  in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16244 = lhs1  in
                 match uu____16244 with
                 | Flex (uu____16247,ctx_u,uu____16249) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16257 ->
                           let uu____16258 = sn_binders env1 bs  in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16258 rhs1
                        in
                     [TERM (ctx_u, sol)]
                  in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16307 = quasi_pattern env1 lhs1  in
                 match uu____16307 with
                 | FStar_Pervasives_Native.None  ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs,uu____16341) ->
                     let uu____16346 = lhs1  in
                     (match uu____16346 with
                      | Flex (t_lhs,ctx_u,args) ->
                          let uu____16361 = occurs_check ctx_u rhs1  in
                          (match uu____16361 with
                           | (uvars,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16412 =
                                   let uu____16420 =
                                     let uu____16422 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16422
                                      in
                                   FStar_Util.Inl uu____16420  in
                                 (uu____16412, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs)
                                     in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1
                                     in
                                  let uu____16450 =
                                    let uu____16452 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs
                                       in
                                    Prims.op_Negation uu____16452  in
                                  if uu____16450
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16479 =
                                       let uu____16487 =
                                         mk_solution env1 lhs1 bs rhs1  in
                                       FStar_Util.Inr uu____16487  in
                                     let uu____16493 =
                                       restrict_all_uvars ctx_u uvars wl1  in
                                     (uu____16479, uu____16493)))))
                  in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16537 = FStar_Syntax_Util.head_and_args rhs1  in
                 match uu____16537 with
                 | (rhs_hd,args) ->
                     let uu____16580 = FStar_Util.prefix args  in
                     (match uu____16580 with
                      | (args_rhs,last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              rhs1.FStar_Syntax_Syntax.pos
                             in
                          let uu____16650 = lhs1  in
                          (match uu____16650 with
                           | Flex (t_lhs,u_lhs,_lhs_args) ->
                               let uu____16654 =
                                 let uu____16665 =
                                   let uu____16672 =
                                     let uu____16675 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16675
                                      in
                                   copy_uvar u_lhs [] uu____16672 wl1  in
                                 match uu____16665 with
                                 | (uu____16702,t_last_arg,wl2) ->
                                     let uu____16705 =
                                       let uu____16712 =
                                         let uu____16713 =
                                           let uu____16722 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg
                                              in
                                           [uu____16722]  in
                                         FStar_List.append bs_lhs uu____16713
                                          in
                                       copy_uvar u_lhs uu____16712 t_res_lhs
                                         wl2
                                        in
                                     (match uu____16705 with
                                      | (uu____16757,lhs',wl3) ->
                                          let uu____16760 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3
                                             in
                                          (match uu____16760 with
                                           | (uu____16777,lhs'_last_arg,wl4)
                                               -> (lhs', lhs'_last_arg, wl4)))
                                  in
                               (match uu____16654 with
                                | (lhs',lhs'_last_arg,wl2) ->
                                    let sol =
                                      let uu____16798 =
                                        let uu____16799 =
                                          let uu____16804 =
                                            let uu____16805 =
                                              let uu____16808 =
                                                let uu____16809 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    lhs'_last_arg
                                                   in
                                                [uu____16809]  in
                                              FStar_Syntax_Syntax.mk_Tm_app
                                                lhs' uu____16808
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16805
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16804)  in
                                        TERM uu____16799  in
                                      [uu____16798]  in
                                    let uu____16834 =
                                      let uu____16841 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs"
                                         in
                                      match uu____16841 with
                                      | (p1,wl3) ->
                                          let uu____16861 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs"
                                             in
                                          (match uu____16861 with
                                           | (p2,wl4) -> ([p1; p2], wl4))
                                       in
                                    (match uu____16834 with
                                     | (sub_probs,wl3) ->
                                         let uu____16893 =
                                           let uu____16894 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16894  in
                                         solve env1 uu____16893))))
                  in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16928 = FStar_Syntax_Util.head_and_args rhs2  in
                   match uu____16928 with
                   | (uu____16946,args) ->
                       (match args with | [] -> false | uu____16982 -> true)
                    in
                 let is_arrow rhs2 =
                   let uu____17001 =
                     let uu____17002 = FStar_Syntax_Subst.compress rhs2  in
                     uu____17002.FStar_Syntax_Syntax.n  in
                   match uu____17001 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____17006 -> true
                   | uu____17022 -> false  in
                 let uu____17024 = quasi_pattern env1 lhs1  in
                 match uu____17024 with
                 | FStar_Pervasives_Native.None  ->
                     let msg =
                       mklstr
                         (fun uu____17043  ->
                            let uu____17044 = prob_to_string env1 orig1  in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____17044)
                        in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                     let uu____17053 = is_app rhs1  in
                     if uu____17053
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____17058 = is_arrow rhs1  in
                        if uu____17058
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             mklstr
                               (fun uu____17071  ->
                                  let uu____17072 = prob_to_string env1 orig1
                                     in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____17072)
                              in
                           giveup_or_defer env1 orig1 wl1 msg))
                  in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB  ->
                   if wl.defer_ok
                   then
                     let uu____17076 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____17076
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV  ->
                   if wl.defer_ok
                   then
                     let uu____17082 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____17082
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ  ->
                   let uu____17087 = lhs  in
                   (match uu____17087 with
                    | Flex (_t1,ctx_uv,args_lhs) ->
                        let uu____17091 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs
                           in
                        (match uu____17091 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs  in
                             let names_to_string1 fvs =
                               let uu____17109 =
                                 let uu____17113 =
                                   FStar_Util.set_elements fvs  in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____17113
                                  in
                               FStar_All.pipe_right uu____17109
                                 (FStar_String.concat ", ")
                                in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders)
                                in
                             let fvs2 = FStar_Syntax_Free.names rhs1  in
                             let uu____17134 = occurs_check ctx_uv rhs1  in
                             (match uu____17134 with
                              | (uvars,occurs_ok,msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17163 =
                                      let uu____17164 =
                                        let uu____17166 =
                                          FStar_Option.get msg  in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17166
                                         in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17164
                                       in
                                    giveup_or_defer env orig wl uu____17163
                                  else
                                    (let uu____17174 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1
                                        in
                                     if uu____17174
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1
                                          in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars wl
                                          in
                                       let uu____17181 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1
                                          in
                                       solve env uu____17181
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            mklstr
                                              (fun uu____17197  ->
                                                 let uu____17198 =
                                                   names_to_string1 fvs2  in
                                                 let uu____17200 =
                                                   names_to_string1 fvs1  in
                                                 let uu____17202 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders)
                                                    in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17198 uu____17200
                                                   uu____17202)
                                             in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17214 ->
                             if wl.defer_ok
                             then
                               let uu____17218 =
                                 FStar_Thunk.mkv "Not a pattern"  in
                               giveup_or_defer env orig wl uu____17218
                             else
                               (let uu____17223 =
                                  try_quasi_pattern orig env wl lhs rhs  in
                                match uu____17223 with
                                | (FStar_Util.Inr sol,wl1) ->
                                    let uu____17249 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17249
                                | (FStar_Util.Inl msg,uu____17251) ->
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
                  let uu____17269 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17269
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____17275 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17275
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17280 =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs)
                   in
                if uu____17280
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
                    (let uu____17287 =
                       FStar_Thunk.mkv "flex-flex non-pattern"  in
                     giveup_or_defer env orig wl uu____17287)
                  else
                    (let uu____17292 =
                       let uu____17309 = quasi_pattern env lhs  in
                       let uu____17316 = quasi_pattern env rhs  in
                       (uu____17309, uu____17316)  in
                     match uu____17292 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                        (binders_rhs,t_res_rhs)) ->
                         let uu____17359 = lhs  in
                         (match uu____17359 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17360;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17362;_},u_lhs,uu____17364)
                              ->
                              let uu____17367 = rhs  in
                              (match uu____17367 with
                               | Flex (uu____17368,u_rhs,uu____17370) ->
                                   let uu____17371 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs)
                                      in
                                   if uu____17371
                                   then
                                     let uu____17378 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl
                                        in
                                     solve env uu____17378
                                   else
                                     (let uu____17381 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      match uu____17381 with
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
                                          let uu____17413 =
                                            let uu____17420 =
                                              let uu____17423 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs
                                                 in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17423
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
                                              uu____17420
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None
                                             in
                                          (match uu____17413 with
                                           | (uu____17429,w,wl1) ->
                                               let w_app =
                                                 let uu____17433 =
                                                   FStar_List.map
                                                     (fun uu____17444  ->
                                                        match uu____17444
                                                        with
                                                        | (z,uu____17452) ->
                                                            let uu____17457 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                z
                                                               in
                                                            FStar_Syntax_Syntax.as_arg
                                                              uu____17457) zs
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   w uu____17433
                                                   w.FStar_Syntax_Syntax.pos
                                                  in
                                               ((let uu____17459 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17459
                                                 then
                                                   let uu____17464 =
                                                     let uu____17468 =
                                                       flex_t_to_string lhs
                                                        in
                                                     let uu____17470 =
                                                       let uu____17474 =
                                                         flex_t_to_string rhs
                                                          in
                                                       let uu____17476 =
                                                         let uu____17480 =
                                                           term_to_string w
                                                            in
                                                         let uu____17482 =
                                                           let uu____17486 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs)
                                                              in
                                                           let uu____17495 =
                                                             let uu____17499
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                in
                                                             let uu____17508
                                                               =
                                                               let uu____17512
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs
                                                                  in
                                                               [uu____17512]
                                                                in
                                                             uu____17499 ::
                                                               uu____17508
                                                              in
                                                           uu____17486 ::
                                                             uu____17495
                                                            in
                                                         uu____17480 ::
                                                           uu____17482
                                                          in
                                                       uu____17474 ::
                                                         uu____17476
                                                        in
                                                     uu____17468 ::
                                                       uu____17470
                                                      in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17464
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17529 =
                                                       let uu____17534 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs))
                                                          in
                                                       (u_lhs, uu____17534)
                                                        in
                                                     TERM uu____17529  in
                                                   let uu____17535 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                      in
                                                   if uu____17535
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17543 =
                                                          let uu____17548 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_rhs,
                                                            uu____17548)
                                                           in
                                                        TERM uu____17543  in
                                                      [s1; s2])
                                                    in
                                                 let uu____17549 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1
                                                    in
                                                 solve env uu____17549))))))
                     | uu____17550 ->
                         let uu____17567 =
                           FStar_Thunk.mkv "flex-flex: non-patterns"  in
                         giveup_or_defer env orig wl uu____17567)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17621 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17621
            then
              let uu____17626 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17628 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17630 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17632 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17626 uu____17628 uu____17630 uu____17632
            else ());
           (let uu____17643 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17643 with
            | (head1,args1) ->
                let uu____17686 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17686 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17756 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17756 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17761 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17761)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17782 =
                         mklstr
                           (fun uu____17793  ->
                              let uu____17794 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17796 = args_to_string args1  in
                              let uu____17800 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17802 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17794 uu____17796 uu____17800
                                uu____17802)
                          in
                       giveup env1 uu____17782 orig
                     else
                       (let uu____17809 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17814 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17814 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17809
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2606_17818 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2606_17818.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2606_17818.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2606_17818.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2606_17818.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2606_17818.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2606_17818.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2606_17818.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2606_17818.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17828 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17828
                                    else solve env1 wl2))
                        else
                          (let uu____17833 = base_and_refinement env1 t1  in
                           match uu____17833 with
                           | (base1,refinement1) ->
                               let uu____17858 = base_and_refinement env1 t2
                                  in
                               (match uu____17858 with
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
                                           let uu____18023 =
                                             FStar_List.fold_right
                                               (fun uu____18063  ->
                                                  fun uu____18064  ->
                                                    match (uu____18063,
                                                            uu____18064)
                                                    with
                                                    | (((a1,uu____18116),
                                                        (a2,uu____18118)),
                                                       (probs,wl3)) ->
                                                        let uu____18167 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18167
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____18023 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18210 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18210
                                                 then
                                                   let uu____18215 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18215
                                                 else ());
                                                (let uu____18221 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18221
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
                                                    (let uu____18248 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18248 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18264 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18264
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18272 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18272))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18297 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18297 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18313 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18313
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18321 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18321)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18349 =
                                           match uu____18349 with
                                           | (prob,reason) ->
                                               ((let uu____18366 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18366
                                                 then
                                                   let uu____18371 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18373 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print2
                                                     "Failed to solve %s because a sub-problem is not solvable without SMT because %s"
                                                     uu____18371 uu____18373
                                                 else ());
                                                (let uu____18379 =
                                                   let uu____18388 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18391 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18388, uu____18391)
                                                    in
                                                 match uu____18379 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18404 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18404 with
                                                      | (head1',uu____18422)
                                                          ->
                                                          let uu____18447 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18447
                                                           with
                                                           | (head2',uu____18465)
                                                               ->
                                                               let uu____18490
                                                                 =
                                                                 let uu____18495
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18496
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18495,
                                                                   uu____18496)
                                                                  in
                                                               (match uu____18490
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18498
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18498
                                                                    then
                                                                    let uu____18503
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18505
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18507
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18509
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18503
                                                                    uu____18505
                                                                    uu____18507
                                                                    uu____18509
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18514
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2694_18522
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2694_18522.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2694_18522.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2694_18522.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2694_18522.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2694_18522.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2694_18522.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2694_18522.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2694_18522.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18524
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18524
                                                                    then
                                                                    let uu____18529
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18529
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18534 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18546 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18546 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18554 =
                                             let uu____18555 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18555.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18554 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18560 -> false  in
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
                                          | uu____18563 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18566 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2714_18602 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2714_18602.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2714_18602.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2714_18602.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2714_18602.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2714_18602.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2714_18602.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2714_18602.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2714_18602.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18678 = destruct_flex_t scrutinee wl1  in
             match uu____18678 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____18689 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18689 with
                  | (xs,pat_term,uu____18705,uu____18706) ->
                      let uu____18711 =
                        FStar_List.fold_left
                          (fun uu____18734  ->
                             fun x  ->
                               match uu____18734 with
                               | (subst,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18755 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18755 with
                                    | (uu____18774,u,wl4) ->
                                        let subst1 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst  in
                                        (subst1, wl4))) ([], wl2) xs
                         in
                      (match uu____18711 with
                       | (subst,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst pat_term  in
                           let uu____18795 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18795 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2755_18812 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2755_18812.wl_deferred_to_tac);
                                    ctr = (uu___2755_18812.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2755_18812.umax_heuristic_ok);
                                    tcenv = (uu___2755_18812.tcenv);
                                    wl_implicits = [];
                                    repr_subcomp_allowed =
                                      (uu___2755_18812.repr_subcomp_allowed)
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18823 = solve env1 wl'  in
                                (match uu____18823 with
                                 | Success (uu____18826,defer_to_tac,imps) ->
                                     let wl'1 =
                                       let uu___2764_18830 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2764_18830.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2764_18830.wl_deferred_to_tac);
                                         ctr = (uu___2764_18830.ctr);
                                         defer_ok =
                                           (uu___2764_18830.defer_ok);
                                         smt_ok = (uu___2764_18830.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2764_18830.umax_heuristic_ok);
                                         tcenv = (uu___2764_18830.tcenv);
                                         wl_implicits =
                                           (uu___2764_18830.wl_implicits);
                                         repr_subcomp_allowed =
                                           (uu___2764_18830.repr_subcomp_allowed)
                                       }  in
                                     let uu____18831 = solve env1 wl'1  in
                                     (match uu____18831 with
                                      | Success
                                          (uu____18834,defer_to_tac',imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18838 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps')
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____18838))
                                      | Failed uu____18844 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18850 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18873 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18873
                 then
                   let uu____18878 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18880 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18878 uu____18880
                 else ());
                (let uu____18885 =
                   let uu____18906 =
                     let uu____18915 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18915)  in
                   let uu____18922 =
                     let uu____18931 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18931)  in
                   (uu____18906, uu____18922)  in
                 match uu____18885 with
                 | ((uu____18961,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18964;
                                   FStar_Syntax_Syntax.vars = uu____18965;_}),
                    (s,t)) ->
                     let uu____19036 =
                       let uu____19038 = is_flex scrutinee  in
                       Prims.op_Negation uu____19038  in
                     if uu____19036
                     then
                       ((let uu____19049 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19049
                         then
                           let uu____19054 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19054
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19073 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19073
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19088 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19088
                           then
                             let uu____19093 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19095 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19093 uu____19095
                           else ());
                          (let pat_discriminates uu___25_19120 =
                             match uu___25_19120 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19136;
                                  FStar_Syntax_Syntax.p = uu____19137;_},FStar_Pervasives_Native.None
                                ,uu____19138) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19152;
                                  FStar_Syntax_Syntax.p = uu____19153;_},FStar_Pervasives_Native.None
                                ,uu____19154) -> true
                             | uu____19181 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19284 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19284 with
                                       | (uu____19286,uu____19287,t') ->
                                           let uu____19305 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19305 with
                                            | (FullMatch ,uu____19317) ->
                                                true
                                            | (HeadMatch
                                               uu____19331,uu____19332) ->
                                                true
                                            | uu____19347 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19384 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19384
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19395 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19395 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19483,uu____19484) ->
                                       branches1
                                   | uu____19629 -> branches  in
                                 let uu____19684 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19693 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19693 with
                                        | (p,uu____19697,uu____19698) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____19727  ->
                                      FStar_Util.Inr uu____19727) uu____19684))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19757 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19757 with
                                | (p,uu____19766,e) ->
                                    ((let uu____19785 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19785
                                      then
                                        let uu____19790 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19792 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19790 uu____19792
                                      else ());
                                     (let uu____19797 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____19812  ->
                                           FStar_Util.Inr uu____19812)
                                        uu____19797)))))
                 | ((s,t),(uu____19815,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19818;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19819;_}))
                     ->
                     let uu____19888 =
                       let uu____19890 = is_flex scrutinee  in
                       Prims.op_Negation uu____19890  in
                     if uu____19888
                     then
                       ((let uu____19901 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19901
                         then
                           let uu____19906 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19906
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19925 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19925
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19940 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19940
                           then
                             let uu____19945 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19947 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19945 uu____19947
                           else ());
                          (let pat_discriminates uu___25_19972 =
                             match uu___25_19972 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19988;
                                  FStar_Syntax_Syntax.p = uu____19989;_},FStar_Pervasives_Native.None
                                ,uu____19990) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____20004;
                                  FStar_Syntax_Syntax.p = uu____20005;_},FStar_Pervasives_Native.None
                                ,uu____20006) -> true
                             | uu____20033 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20136 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20136 with
                                       | (uu____20138,uu____20139,t') ->
                                           let uu____20157 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20157 with
                                            | (FullMatch ,uu____20169) ->
                                                true
                                            | (HeadMatch
                                               uu____20183,uu____20184) ->
                                                true
                                            | uu____20199 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20236 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20236
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20247 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20247 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20335,uu____20336) ->
                                       branches1
                                   | uu____20481 -> branches  in
                                 let uu____20536 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20545 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20545 with
                                        | (p,uu____20549,uu____20550) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun uu____20579  ->
                                      FStar_Util.Inr uu____20579) uu____20536))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20609 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20609 with
                                | (p,uu____20618,e) ->
                                    ((let uu____20637 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20637
                                      then
                                        let uu____20642 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20644 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20642 uu____20644
                                      else ());
                                     (let uu____20649 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun uu____20664  ->
                                           FStar_Util.Inr uu____20664)
                                        uu____20649)))))
                 | uu____20665 ->
                     ((let uu____20687 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20687
                       then
                         let uu____20692 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20694 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20692 uu____20694
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20740 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20740
            then
              let uu____20745 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20747 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20749 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20751 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20745 uu____20747 uu____20749 uu____20751
            else ());
           (let uu____20756 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20756 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20787,uu____20788) ->
                     let rec may_relate head =
                       let uu____20816 =
                         let uu____20817 = FStar_Syntax_Subst.compress head
                            in
                         uu____20817.FStar_Syntax_Syntax.n  in
                       match uu____20816 with
                       | FStar_Syntax_Syntax.Tm_name uu____20821 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20823 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20848 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20848 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20850 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20853
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20854 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20857,uu____20858) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20900) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20906) ->
                           may_relate t
                       | uu____20911 -> false  in
                     let uu____20913 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20913 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20926 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20926
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20936 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20936
                          then
                            let uu____20939 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20939 with
                             | (guard,wl2) ->
                                 let uu____20946 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20946)
                          else
                            (let uu____20949 =
                               mklstr
                                 (fun uu____20960  ->
                                    let uu____20961 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20963 =
                                      let uu____20965 =
                                        let uu____20969 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20969
                                          (fun x  ->
                                             let uu____20976 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20976)
                                         in
                                      FStar_Util.dflt "" uu____20965  in
                                    let uu____20981 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20983 =
                                      let uu____20985 =
                                        let uu____20989 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20989
                                          (fun x  ->
                                             let uu____20996 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20996)
                                         in
                                      FStar_Util.dflt "" uu____20985  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20961 uu____20963 uu____20981
                                      uu____20983)
                                in
                             giveup env1 uu____20949 orig))
                 | (HeadMatch (true ),uu____21002) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____21017 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____21017 with
                        | (guard,wl2) ->
                            let uu____21024 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____21024)
                     else
                       (let uu____21027 =
                          mklstr
                            (fun uu____21034  ->
                               let uu____21035 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____21037 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____21035 uu____21037)
                           in
                        giveup env1 uu____21027 orig)
                 | (uu____21040,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2946_21054 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2946_21054.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2946_21054.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2946_21054.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2946_21054.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2946_21054.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2946_21054.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2946_21054.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2946_21054.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____21081 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____21081
          then
            let uu____21084 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____21084
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____21090 =
                let uu____21093 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21093  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____21090 t1);
             (let uu____21112 =
                let uu____21115 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21115  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____21112 t2);
             (let uu____21134 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____21134
              then
                let uu____21138 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____21140 =
                  let uu____21142 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____21144 =
                    let uu____21146 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____21146  in
                  Prims.op_Hat uu____21142 uu____21144  in
                let uu____21149 =
                  let uu____21151 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____21153 =
                    let uu____21155 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____21155  in
                  Prims.op_Hat uu____21151 uu____21153  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21138 uu____21140 uu____21149
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21162,uu____21163) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21179,FStar_Syntax_Syntax.Tm_delayed uu____21180) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21196,uu____21197) ->
                  let uu____21224 =
                    let uu___2977_21225 = problem  in
                    let uu____21226 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2977_21225.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21226;
                      FStar_TypeChecker_Common.relation =
                        (uu___2977_21225.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2977_21225.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2977_21225.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2977_21225.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2977_21225.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2977_21225.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2977_21225.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2977_21225.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21224 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21227,uu____21228) ->
                  let uu____21235 =
                    let uu___2983_21236 = problem  in
                    let uu____21237 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2983_21236.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21237;
                      FStar_TypeChecker_Common.relation =
                        (uu___2983_21236.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2983_21236.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2983_21236.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2983_21236.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2983_21236.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2983_21236.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2983_21236.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2983_21236.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21235 wl
              | (uu____21238,FStar_Syntax_Syntax.Tm_ascribed uu____21239) ->
                  let uu____21266 =
                    let uu___2989_21267 = problem  in
                    let uu____21268 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2989_21267.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2989_21267.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2989_21267.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21268;
                      FStar_TypeChecker_Common.element =
                        (uu___2989_21267.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2989_21267.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2989_21267.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2989_21267.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2989_21267.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2989_21267.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21266 wl
              | (uu____21269,FStar_Syntax_Syntax.Tm_meta uu____21270) ->
                  let uu____21277 =
                    let uu___2995_21278 = problem  in
                    let uu____21279 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2995_21278.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2995_21278.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2995_21278.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21279;
                      FStar_TypeChecker_Common.element =
                        (uu___2995_21278.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2995_21278.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2995_21278.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2995_21278.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2995_21278.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2995_21278.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21277 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21281),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21283)) ->
                  let uu____21292 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21292
              | (FStar_Syntax_Syntax.Tm_bvar uu____21293,uu____21294) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21296,FStar_Syntax_Syntax.Tm_bvar uu____21297) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___26_21367 =
                    match uu___26_21367 with
                    | [] -> c
                    | bs ->
                        let uu____21395 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21395
                     in
                  let uu____21406 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21406 with
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
                                    let uu____21555 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21555
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
                  let mk_t t l uu___27_21644 =
                    match uu___27_21644 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21686 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21686 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst  ->
                                  let uu____21831 =
                                    FStar_Syntax_Subst.subst subst tbody11
                                     in
                                  let uu____21832 =
                                    FStar_Syntax_Subst.subst subst tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21831
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21832 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21834,uu____21835) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21866 -> true
                    | uu____21886 -> false  in
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
                      (let uu____21946 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3097_21954 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3097_21954.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3097_21954.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3097_21954.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3097_21954.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3097_21954.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3097_21954.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3097_21954.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3097_21954.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3097_21954.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3097_21954.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3097_21954.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3097_21954.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3097_21954.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3097_21954.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3097_21954.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3097_21954.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3097_21954.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3097_21954.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3097_21954.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3097_21954.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3097_21954.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3097_21954.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3097_21954.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3097_21954.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3097_21954.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3097_21954.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3097_21954.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3097_21954.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3097_21954.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3097_21954.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3097_21954.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3097_21954.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3097_21954.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3097_21954.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3097_21954.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3097_21954.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3097_21954.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3097_21954.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3097_21954.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3097_21954.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3097_21954.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3097_21954.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3097_21954.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3097_21954.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____21946 with
                       | (uu____21959,ty,uu____21961) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21970 =
                                 let uu____21971 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21971.FStar_Syntax_Syntax.n  in
                               match uu____21970 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21974 ->
                                   let uu____21981 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21981
                               | uu____21982 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21985 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21985
                             then
                               let uu____21990 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21992 =
                                 let uu____21994 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21994
                                  in
                               let uu____21995 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21990 uu____21992 uu____21995
                             else ());
                            r1))
                     in
                  let uu____22000 =
                    let uu____22017 = maybe_eta t1  in
                    let uu____22024 = maybe_eta t2  in
                    (uu____22017, uu____22024)  in
                  (match uu____22000 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3118_22066 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3118_22066.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3118_22066.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3118_22066.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3118_22066.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3118_22066.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3118_22066.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3118_22066.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3118_22066.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22087 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22087
                       then
                         let uu____22090 = destruct_flex_t not_abs wl  in
                         (match uu____22090 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3135_22107 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3135_22107.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3135_22107.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3135_22107.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3135_22107.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3135_22107.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3135_22107.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3135_22107.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3135_22107.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22110 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22110 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22133 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22133
                       then
                         let uu____22136 = destruct_flex_t not_abs wl  in
                         (match uu____22136 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3135_22153 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3135_22153.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3135_22153.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3135_22153.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3135_22153.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3135_22153.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3135_22153.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3135_22153.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3135_22153.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22156 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22156 orig))
                   | uu____22159 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22177,FStar_Syntax_Syntax.Tm_abs uu____22178) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22209 -> true
                    | uu____22229 -> false  in
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
                      (let uu____22289 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3097_22297 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3097_22297.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3097_22297.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3097_22297.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3097_22297.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3097_22297.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3097_22297.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3097_22297.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3097_22297.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3097_22297.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3097_22297.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3097_22297.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3097_22297.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3097_22297.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3097_22297.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3097_22297.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3097_22297.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3097_22297.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3097_22297.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3097_22297.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3097_22297.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3097_22297.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3097_22297.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3097_22297.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3097_22297.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3097_22297.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3097_22297.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3097_22297.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3097_22297.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3097_22297.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3097_22297.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3097_22297.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3097_22297.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3097_22297.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3097_22297.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3097_22297.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3097_22297.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3097_22297.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3097_22297.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3097_22297.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3097_22297.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3097_22297.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3097_22297.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3097_22297.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3097_22297.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____22289 with
                       | (uu____22302,ty,uu____22304) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22313 =
                                 let uu____22314 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22314.FStar_Syntax_Syntax.n  in
                               match uu____22313 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22317 ->
                                   let uu____22324 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22324
                               | uu____22325 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22328 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22328
                             then
                               let uu____22333 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22335 =
                                 let uu____22337 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22337
                                  in
                               let uu____22338 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22333 uu____22335 uu____22338
                             else ());
                            r1))
                     in
                  let uu____22343 =
                    let uu____22360 = maybe_eta t1  in
                    let uu____22367 = maybe_eta t2  in
                    (uu____22360, uu____22367)  in
                  (match uu____22343 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3118_22409 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3118_22409.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3118_22409.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3118_22409.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3118_22409.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3118_22409.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3118_22409.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3118_22409.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3118_22409.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22430 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22430
                       then
                         let uu____22433 = destruct_flex_t not_abs wl  in
                         (match uu____22433 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3135_22450 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3135_22450.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3135_22450.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3135_22450.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3135_22450.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3135_22450.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3135_22450.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3135_22450.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3135_22450.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22453 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22453 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22476 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22476
                       then
                         let uu____22479 = destruct_flex_t not_abs wl  in
                         (match uu____22479 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3135_22496 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3135_22496.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3135_22496.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3135_22496.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3135_22496.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3135_22496.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3135_22496.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3135_22496.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3135_22496.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22499 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22499 orig))
                   | uu____22502 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22532 =
                    let uu____22537 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22537 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3158_22565 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3158_22565.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3158_22565.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3160_22567 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3160_22567.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3160_22567.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22568,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3158_22583 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3158_22583.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3158_22583.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3160_22585 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3160_22585.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3160_22585.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22586 -> (x1, x2)  in
                  (match uu____22532 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22605 = as_refinement false env t11  in
                       (match uu____22605 with
                        | (x12,phi11) ->
                            let uu____22613 = as_refinement false env t21  in
                            (match uu____22613 with
                             | (x22,phi21) ->
                                 ((let uu____22622 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22622
                                   then
                                     ((let uu____22627 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22629 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22631 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22627
                                         uu____22629 uu____22631);
                                      (let uu____22634 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22636 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22638 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22634
                                         uu____22636 uu____22638))
                                   else ());
                                  (let uu____22643 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22643 with
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
                                         let uu____22714 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22714
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22726 =
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
                                         (let uu____22739 =
                                            let uu____22742 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22742
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22739
                                            (p_guard base_prob));
                                         (let uu____22761 =
                                            let uu____22764 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22764
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22761
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22783 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22783)
                                          in
                                       let has_uvars =
                                         (let uu____22788 =
                                            let uu____22790 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22790
                                             in
                                          Prims.op_Negation uu____22788) ||
                                           (let uu____22794 =
                                              let uu____22796 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22796
                                               in
                                            Prims.op_Negation uu____22794)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22800 =
                                           let uu____22805 =
                                             let uu____22814 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22814]  in
                                           mk_t_problem wl1 uu____22805 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22800 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22837 =
                                                solve env1
                                                  (let uu___3203_22839 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3203_22839.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3203_22839.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3203_22839.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3203_22839.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3203_22839.tcenv);
                                                     wl_implicits =
                                                       (uu___3203_22839.wl_implicits);
                                                     repr_subcomp_allowed =
                                                       (uu___3203_22839.repr_subcomp_allowed)
                                                   })
                                                 in
                                              (match uu____22837 with
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
                                                   (uu____22854,defer_to_tac,uu____22856)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22861 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22861
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3219_22870 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3219_22870.attempting);
                                                         wl_deferred =
                                                           (uu___3219_22870.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3219_22870.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3219_22870.defer_ok);
                                                         smt_ok =
                                                           (uu___3219_22870.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3219_22870.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3219_22870.tcenv);
                                                         wl_implicits =
                                                           (uu___3219_22870.wl_implicits);
                                                         repr_subcomp_allowed
                                                           =
                                                           (uu___3219_22870.repr_subcomp_allowed)
                                                       }  in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac []
                                                        in
                                                     let uu____22873 =
                                                       attempt [base_prob]
                                                         wl5
                                                        in
                                                     solve env1 uu____22873))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22876,FStar_Syntax_Syntax.Tm_uvar uu____22877) ->
                  let uu____22902 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22902 with
                   | (t11,wl1) ->
                       let uu____22909 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22909 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22918;
                    FStar_Syntax_Syntax.pos = uu____22919;
                    FStar_Syntax_Syntax.vars = uu____22920;_},uu____22921),FStar_Syntax_Syntax.Tm_uvar
                 uu____22922) ->
                  let uu____22971 = ensure_no_uvar_subst t1 wl  in
                  (match uu____22971 with
                   | (t11,wl1) ->
                       let uu____22978 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____22978 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22987,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22988;
                    FStar_Syntax_Syntax.pos = uu____22989;
                    FStar_Syntax_Syntax.vars = uu____22990;_},uu____22991))
                  ->
                  let uu____23040 = ensure_no_uvar_subst t1 wl  in
                  (match uu____23040 with
                   | (t11,wl1) ->
                       let uu____23047 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____23047 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23056;
                    FStar_Syntax_Syntax.pos = uu____23057;
                    FStar_Syntax_Syntax.vars = uu____23058;_},uu____23059),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23060;
                    FStar_Syntax_Syntax.pos = uu____23061;
                    FStar_Syntax_Syntax.vars = uu____23062;_},uu____23063))
                  ->
                  let uu____23136 = ensure_no_uvar_subst t1 wl  in
                  (match uu____23136 with
                   | (t11,wl1) ->
                       let uu____23143 = ensure_no_uvar_subst t2 wl1  in
                       (match uu____23143 with
                        | (t21,wl2) ->
                            let f1 = destruct_flex_t' t11  in
                            let f2 = destruct_flex_t' t21  in
                            solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23152,uu____23153) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23166 = destruct_flex_t t1 wl  in
                  (match uu____23166 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23173;
                    FStar_Syntax_Syntax.pos = uu____23174;
                    FStar_Syntax_Syntax.vars = uu____23175;_},uu____23176),uu____23177)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23214 = destruct_flex_t t1 wl  in
                  (match uu____23214 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23221,FStar_Syntax_Syntax.Tm_uvar uu____23222) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23235,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23236;
                    FStar_Syntax_Syntax.pos = uu____23237;
                    FStar_Syntax_Syntax.vars = uu____23238;_},uu____23239))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23276,FStar_Syntax_Syntax.Tm_arrow uu____23277) ->
                  solve_t' env
                    (let uu___3322_23305 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3322_23305.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3322_23305.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3322_23305.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3322_23305.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3322_23305.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3322_23305.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3322_23305.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3322_23305.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3322_23305.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23306;
                    FStar_Syntax_Syntax.pos = uu____23307;
                    FStar_Syntax_Syntax.vars = uu____23308;_},uu____23309),FStar_Syntax_Syntax.Tm_arrow
                 uu____23310) ->
                  solve_t' env
                    (let uu___3322_23362 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3322_23362.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3322_23362.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3322_23362.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3322_23362.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3322_23362.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3322_23362.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3322_23362.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3322_23362.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3322_23362.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23363,FStar_Syntax_Syntax.Tm_uvar uu____23364) ->
                  let uu____23377 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23377
              | (uu____23378,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23379;
                    FStar_Syntax_Syntax.pos = uu____23380;
                    FStar_Syntax_Syntax.vars = uu____23381;_},uu____23382))
                  ->
                  let uu____23419 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23419
              | (FStar_Syntax_Syntax.Tm_uvar uu____23420,uu____23421) ->
                  let uu____23434 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23434
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23435;
                    FStar_Syntax_Syntax.pos = uu____23436;
                    FStar_Syntax_Syntax.vars = uu____23437;_},uu____23438),uu____23439)
                  ->
                  let uu____23476 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23476
              | (FStar_Syntax_Syntax.Tm_refine uu____23477,uu____23478) ->
                  let t21 =
                    let uu____23486 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23486  in
                  solve_t env
                    (let uu___3357_23512 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3357_23512.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3357_23512.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3357_23512.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3357_23512.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3357_23512.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3357_23512.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3357_23512.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3357_23512.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3357_23512.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23513,FStar_Syntax_Syntax.Tm_refine uu____23514) ->
                  let t11 =
                    let uu____23522 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23522  in
                  solve_t env
                    (let uu___3364_23548 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3364_23548.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3364_23548.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3364_23548.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3364_23548.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3364_23548.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3364_23548.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3364_23548.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3364_23548.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3364_23548.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23630 =
                    let uu____23631 = guard_of_prob env wl problem t1 t2  in
                    match uu____23631 with
                    | (guard,wl1) ->
                        let uu____23638 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23638
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23857 = br1  in
                        (match uu____23857 with
                         | (p1,w1,uu____23886) ->
                             let uu____23903 = br2  in
                             (match uu____23903 with
                              | (p2,w2,uu____23926) ->
                                  let uu____23931 =
                                    let uu____23933 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23933  in
                                  if uu____23931
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23960 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23960 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23997 = br2  in
                                         (match uu____23997 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____24030 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____24030
                                                 in
                                              let uu____24035 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____24066,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____24087) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____24146 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____24146 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____24035
                                                (fun uu____24218  ->
                                                   match uu____24218 with
                                                   | (wprobs,wl2) ->
                                                       let uu____24255 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____24255
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24276
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24276
                                                              then
                                                                let uu____24281
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24283
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24281
                                                                  uu____24283
                                                              else ());
                                                             (let uu____24289
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24289
                                                                (fun
                                                                   uu____24325
                                                                    ->
                                                                   match uu____24325
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
                    | uu____24454 -> FStar_Pervasives_Native.None  in
                  let uu____24495 = solve_branches wl brs1 brs2  in
                  (match uu____24495 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24521 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24521 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24548 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24548 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24582 =
                                FStar_List.map
                                  (fun uu____24594  ->
                                     match uu____24594 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24582  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24603 =
                              let uu____24604 =
                                let uu____24605 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24605
                                  (let uu___3463_24613 = wl3  in
                                   {
                                     attempting =
                                       (uu___3463_24613.attempting);
                                     wl_deferred =
                                       (uu___3463_24613.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3463_24613.wl_deferred_to_tac);
                                     ctr = (uu___3463_24613.ctr);
                                     defer_ok = (uu___3463_24613.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3463_24613.umax_heuristic_ok);
                                     tcenv = (uu___3463_24613.tcenv);
                                     wl_implicits =
                                       (uu___3463_24613.wl_implicits);
                                     repr_subcomp_allowed =
                                       (uu___3463_24613.repr_subcomp_allowed)
                                   })
                                 in
                              solve env uu____24604  in
                            (match uu____24603 with
                             | Success (ds,ds',imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24619 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24628 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24628 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24631,uu____24632) ->
                  let head1 =
                    let uu____24656 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24656
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24702 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24702
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24748 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24748
                    then
                      let uu____24752 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24754 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24756 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24752 uu____24754 uu____24756
                    else ());
                   (let no_free_uvars t =
                      (let uu____24770 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24770) &&
                        (let uu____24774 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24774)
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
                      let uu____24793 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24793 = FStar_Syntax_Util.Equal  in
                    let uu____24794 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24794
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24798 = equal t1 t2  in
                         (if uu____24798
                          then
                            let uu____24801 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24801
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24806 =
                            let uu____24813 = equal t1 t2  in
                            if uu____24813
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24826 = mk_eq2 wl env orig t1 t2  in
                               match uu____24826 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24806 with
                          | (guard,wl1) ->
                              let uu____24847 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24847))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24850,uu____24851) ->
                  let head1 =
                    let uu____24859 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24859
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24905 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24905
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24951 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24951
                    then
                      let uu____24955 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24957 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24959 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24955 uu____24957 uu____24959
                    else ());
                   (let no_free_uvars t =
                      (let uu____24973 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24973) &&
                        (let uu____24977 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24977)
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
                      let uu____24996 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24996 = FStar_Syntax_Util.Equal  in
                    let uu____24997 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24997
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25001 = equal t1 t2  in
                         (if uu____25001
                          then
                            let uu____25004 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25004
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25009 =
                            let uu____25016 = equal t1 t2  in
                            if uu____25016
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25029 = mk_eq2 wl env orig t1 t2  in
                               match uu____25029 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25009 with
                          | (guard,wl1) ->
                              let uu____25050 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25050))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____25053,uu____25054) ->
                  let head1 =
                    let uu____25056 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25056
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25102 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25102
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25148 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25148
                    then
                      let uu____25152 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25154 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25156 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25152 uu____25154 uu____25156
                    else ());
                   (let no_free_uvars t =
                      (let uu____25170 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25170) &&
                        (let uu____25174 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25174)
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
                      let uu____25193 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25193 = FStar_Syntax_Util.Equal  in
                    let uu____25194 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25194
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25198 = equal t1 t2  in
                         (if uu____25198
                          then
                            let uu____25201 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25201
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25206 =
                            let uu____25213 = equal t1 t2  in
                            if uu____25213
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25226 = mk_eq2 wl env orig t1 t2  in
                               match uu____25226 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25206 with
                          | (guard,wl1) ->
                              let uu____25247 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25247))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25250,uu____25251) ->
                  let head1 =
                    let uu____25253 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25253
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25299 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25299
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25345 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25345
                    then
                      let uu____25349 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25351 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25353 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25349 uu____25351 uu____25353
                    else ());
                   (let no_free_uvars t =
                      (let uu____25367 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25367) &&
                        (let uu____25371 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25371)
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
                      let uu____25390 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25390 = FStar_Syntax_Util.Equal  in
                    let uu____25391 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25391
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25395 = equal t1 t2  in
                         (if uu____25395
                          then
                            let uu____25398 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25398
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25403 =
                            let uu____25410 = equal t1 t2  in
                            if uu____25410
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25423 = mk_eq2 wl env orig t1 t2  in
                               match uu____25423 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25403 with
                          | (guard,wl1) ->
                              let uu____25444 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25444))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25447,uu____25448) ->
                  let head1 =
                    let uu____25450 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25450
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25490 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25490
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25530 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25530
                    then
                      let uu____25534 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25536 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25538 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25534 uu____25536 uu____25538
                    else ());
                   (let no_free_uvars t =
                      (let uu____25552 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25552) &&
                        (let uu____25556 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25556)
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
                      let uu____25575 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25575 = FStar_Syntax_Util.Equal  in
                    let uu____25576 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25576
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25580 = equal t1 t2  in
                         (if uu____25580
                          then
                            let uu____25583 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25583
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25588 =
                            let uu____25595 = equal t1 t2  in
                            if uu____25595
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25608 = mk_eq2 wl env orig t1 t2  in
                               match uu____25608 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25588 with
                          | (guard,wl1) ->
                              let uu____25629 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25629))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25632,uu____25633) ->
                  let head1 =
                    let uu____25651 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25651
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25691 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25691
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25731 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25731
                    then
                      let uu____25735 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25737 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25739 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25735 uu____25737 uu____25739
                    else ());
                   (let no_free_uvars t =
                      (let uu____25753 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25753) &&
                        (let uu____25757 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25757)
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
                      let uu____25776 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25776 = FStar_Syntax_Util.Equal  in
                    let uu____25777 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25777
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25781 = equal t1 t2  in
                         (if uu____25781
                          then
                            let uu____25784 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25784
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25789 =
                            let uu____25796 = equal t1 t2  in
                            if uu____25796
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25809 = mk_eq2 wl env orig t1 t2  in
                               match uu____25809 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25789 with
                          | (guard,wl1) ->
                              let uu____25830 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25830))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25833,FStar_Syntax_Syntax.Tm_match uu____25834) ->
                  let head1 =
                    let uu____25858 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25858
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25898 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25898
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25938 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25938
                    then
                      let uu____25942 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25944 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25946 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25942 uu____25944 uu____25946
                    else ());
                   (let no_free_uvars t =
                      (let uu____25960 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25960) &&
                        (let uu____25964 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25964)
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
                      let uu____25983 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25983 = FStar_Syntax_Util.Equal  in
                    let uu____25984 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25984
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25988 = equal t1 t2  in
                         (if uu____25988
                          then
                            let uu____25991 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25991
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25996 =
                            let uu____26003 = equal t1 t2  in
                            if uu____26003
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26016 = mk_eq2 wl env orig t1 t2  in
                               match uu____26016 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25996 with
                          | (guard,wl1) ->
                              let uu____26037 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26037))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26040,FStar_Syntax_Syntax.Tm_uinst uu____26041) ->
                  let head1 =
                    let uu____26049 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26049
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26089 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26089
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26129 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26129
                    then
                      let uu____26133 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26135 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26137 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26133 uu____26135 uu____26137
                    else ());
                   (let no_free_uvars t =
                      (let uu____26151 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26151) &&
                        (let uu____26155 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26155)
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
                      let uu____26174 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26174 = FStar_Syntax_Util.Equal  in
                    let uu____26175 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26175
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26179 = equal t1 t2  in
                         (if uu____26179
                          then
                            let uu____26182 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26182
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26187 =
                            let uu____26194 = equal t1 t2  in
                            if uu____26194
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26207 = mk_eq2 wl env orig t1 t2  in
                               match uu____26207 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26187 with
                          | (guard,wl1) ->
                              let uu____26228 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26228))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26231,FStar_Syntax_Syntax.Tm_name uu____26232) ->
                  let head1 =
                    let uu____26234 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26234
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26274 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26274
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26314 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26314
                    then
                      let uu____26318 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26320 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26322 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26318 uu____26320 uu____26322
                    else ());
                   (let no_free_uvars t =
                      (let uu____26336 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26336) &&
                        (let uu____26340 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26340)
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
                      let uu____26359 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26359 = FStar_Syntax_Util.Equal  in
                    let uu____26360 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26360
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26364 = equal t1 t2  in
                         (if uu____26364
                          then
                            let uu____26367 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26367
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26372 =
                            let uu____26379 = equal t1 t2  in
                            if uu____26379
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26392 = mk_eq2 wl env orig t1 t2  in
                               match uu____26392 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26372 with
                          | (guard,wl1) ->
                              let uu____26413 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26413))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26416,FStar_Syntax_Syntax.Tm_constant uu____26417) ->
                  let head1 =
                    let uu____26419 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26419
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26459 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26459
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26499 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26499
                    then
                      let uu____26503 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26505 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26507 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26503 uu____26505 uu____26507
                    else ());
                   (let no_free_uvars t =
                      (let uu____26521 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26521) &&
                        (let uu____26525 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26525)
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
                      let uu____26544 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26544 = FStar_Syntax_Util.Equal  in
                    let uu____26545 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26545
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26549 = equal t1 t2  in
                         (if uu____26549
                          then
                            let uu____26552 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26552
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26557 =
                            let uu____26564 = equal t1 t2  in
                            if uu____26564
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26577 = mk_eq2 wl env orig t1 t2  in
                               match uu____26577 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26557 with
                          | (guard,wl1) ->
                              let uu____26598 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26598))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26601,FStar_Syntax_Syntax.Tm_fvar uu____26602) ->
                  let head1 =
                    let uu____26604 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26604
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26650 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26650
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26696 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26696
                    then
                      let uu____26700 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26702 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26704 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26700 uu____26702 uu____26704
                    else ());
                   (let no_free_uvars t =
                      (let uu____26718 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26718) &&
                        (let uu____26722 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26722)
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
                      let uu____26741 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26741 = FStar_Syntax_Util.Equal  in
                    let uu____26742 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26742
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26746 = equal t1 t2  in
                         (if uu____26746
                          then
                            let uu____26749 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26749
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26754 =
                            let uu____26761 = equal t1 t2  in
                            if uu____26761
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26774 = mk_eq2 wl env orig t1 t2  in
                               match uu____26774 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26754 with
                          | (guard,wl1) ->
                              let uu____26795 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26795))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26798,FStar_Syntax_Syntax.Tm_app uu____26799) ->
                  let head1 =
                    let uu____26817 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26817
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26857 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26857
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26897 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26897
                    then
                      let uu____26901 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26903 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26905 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26901 uu____26903 uu____26905
                    else ());
                   (let no_free_uvars t =
                      (let uu____26919 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26919) &&
                        (let uu____26923 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26923)
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
                      let uu____26942 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26942 = FStar_Syntax_Util.Equal  in
                    let uu____26943 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26943
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26947 = equal t1 t2  in
                         (if uu____26947
                          then
                            let uu____26950 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26950
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26955 =
                            let uu____26962 = equal t1 t2  in
                            if uu____26962
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26975 = mk_eq2 wl env orig t1 t2  in
                               match uu____26975 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26955 with
                          | (guard,wl1) ->
                              let uu____26996 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26996))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26999,FStar_Syntax_Syntax.Tm_let uu____27000) ->
                  let uu____27027 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____27027
                  then
                    let uu____27030 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____27030
                  else
                    (let uu____27033 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____27033 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____27036,uu____27037) ->
                  let uu____27051 =
                    let uu____27057 =
                      let uu____27059 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____27061 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____27063 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____27065 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27059 uu____27061 uu____27063 uu____27065
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27057)
                     in
                  FStar_Errors.raise_error uu____27051
                    t1.FStar_Syntax_Syntax.pos
              | (uu____27069,FStar_Syntax_Syntax.Tm_let uu____27070) ->
                  let uu____27084 =
                    let uu____27090 =
                      let uu____27092 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____27094 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____27096 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____27098 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____27092 uu____27094 uu____27096 uu____27098
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____27090)
                     in
                  FStar_Errors.raise_error uu____27084
                    t1.FStar_Syntax_Syntax.pos
              | uu____27102 ->
                  let uu____27107 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____27107 orig))))

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
          (let uu____27173 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____27173
           then
             let uu____27178 =
               let uu____27180 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____27180  in
             let uu____27181 =
               let uu____27183 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____27183  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27178 uu____27181
           else ());
          (let uu____27187 =
             let uu____27189 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____27189  in
           if uu____27187
           then
             let uu____27192 =
               mklstr
                 (fun uu____27199  ->
                    let uu____27200 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____27202 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27200 uu____27202)
                in
             giveup env uu____27192 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27224 =
                  mklstr
                    (fun uu____27231  ->
                       let uu____27232 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27234 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27232 uu____27234)
                   in
                giveup env uu____27224 orig)
             else
               (let uu____27239 =
                  FStar_List.fold_left2
                    (fun uu____27260  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27260 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27281 =
                                 let uu____27286 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27287 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27286
                                   FStar_TypeChecker_Common.EQ uu____27287
                                   "effect universes"
                                  in
                               (match uu____27281 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27239 with
                | (univ_sub_probs,wl1) ->
                    let uu____27307 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27307 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27315 =
                           FStar_List.fold_right2
                             (fun uu____27352  ->
                                fun uu____27353  ->
                                  fun uu____27354  ->
                                    match (uu____27352, uu____27353,
                                            uu____27354)
                                    with
                                    | ((a1,uu____27398),(a2,uu____27400),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27433 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27433 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27315 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27460 =
                                  let uu____27463 =
                                    let uu____27466 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27466
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27463
                                   in
                                FStar_List.append univ_sub_probs uu____27460
                                 in
                              let guard =
                                let guard =
                                  let uu____27488 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27488  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3616_27497 = wl3  in
                                {
                                  attempting = (uu___3616_27497.attempting);
                                  wl_deferred = (uu___3616_27497.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3616_27497.wl_deferred_to_tac);
                                  ctr = (uu___3616_27497.ctr);
                                  defer_ok = (uu___3616_27497.defer_ok);
                                  smt_ok = (uu___3616_27497.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3616_27497.umax_heuristic_ok);
                                  tcenv = (uu___3616_27497.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits);
                                  repr_subcomp_allowed =
                                    (uu___3616_27497.repr_subcomp_allowed)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27499 = attempt sub_probs wl5  in
                              solve env uu____27499))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____27517 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____27517
           then
             let uu____27522 =
               let uu____27524 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27524
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27526 =
               let uu____27528 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27528
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27522 uu____27526
           else ());
          (let uu____27533 =
             let uu____27538 =
               let uu____27543 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27543
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27538
               (fun uu____27560  ->
                  match uu____27560 with
                  | (c,g) ->
                      let uu____27571 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27571, g))
              in
           match uu____27533 with
           | (c12,g_lift) ->
               ((let uu____27575 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27575
                 then
                   let uu____27580 =
                     let uu____27582 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27582
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27584 =
                     let uu____27586 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27586
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27580 uu____27584
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3636_27596 = wl  in
                     {
                       attempting = (uu___3636_27596.attempting);
                       wl_deferred = (uu___3636_27596.wl_deferred);
                       wl_deferred_to_tac =
                         (uu___3636_27596.wl_deferred_to_tac);
                       ctr = (uu___3636_27596.ctr);
                       defer_ok = (uu___3636_27596.defer_ok);
                       smt_ok = (uu___3636_27596.smt_ok);
                       umax_heuristic_ok =
                         (uu___3636_27596.umax_heuristic_ok);
                       tcenv = (uu___3636_27596.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits);
                       repr_subcomp_allowed =
                         (uu___3636_27596.repr_subcomp_allowed)
                     }  in
                   let uu____27597 =
                     let rec is_uvar t =
                       let uu____27611 =
                         let uu____27612 = FStar_Syntax_Subst.compress t  in
                         uu____27612.FStar_Syntax_Syntax.n  in
                       match uu____27611 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27616 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27631) ->
                           is_uvar t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27637) ->
                           is_uvar t1
                       | uu____27662 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27696  ->
                          fun uu____27697  ->
                            fun uu____27698  ->
                              match (uu____27696, uu____27697, uu____27698)
                              with
                              | ((a1,uu____27742),(a2,uu____27744),(is_sub_probs,wl2))
                                  ->
                                  let uu____27777 = is_uvar a1  in
                                  if uu____27777
                                  then
                                    ((let uu____27787 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27787
                                      then
                                        let uu____27792 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27794 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27792 uu____27794
                                      else ());
                                     (let uu____27799 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27799 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27597 with
                   | (is_sub_probs,wl2) ->
                       let uu____27827 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27827 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27835 =
                              let uu____27840 =
                                let uu____27841 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27841
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27840
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27835 with
                             | (uu____27848,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27859 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27861 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27859 s uu____27861
                                    in
                                 let uu____27864 =
                                   let uu____27893 =
                                     let uu____27894 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27894.FStar_Syntax_Syntax.n  in
                                   match uu____27893 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27954 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27954 with
                                        | (bs',c3) ->
                                            let a = FStar_List.hd bs'  in
                                            let bs1 = FStar_List.tail bs'  in
                                            let uu____28017 =
                                              let uu____28036 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____28036
                                                (fun uu____28140  ->
                                                   match uu____28140 with
                                                   | (l1,l2) ->
                                                       let uu____28213 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____28213))
                                               in
                                            (match uu____28017 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____28318 ->
                                       let uu____28319 =
                                         let uu____28325 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____28325)
                                          in
                                       FStar_Errors.raise_error uu____28319 r
                                    in
                                 (match uu____27864 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____28401 =
                                        let uu____28408 =
                                          let uu____28409 =
                                            let uu____28410 =
                                              let uu____28417 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____28417,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____28410
                                             in
                                          [uu____28409]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____28408
                                          (fun b  ->
                                             let uu____28433 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____28435 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28437 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____28433 uu____28435
                                               uu____28437) r
                                         in
                                      (match uu____28401 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____28447 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____28447
                                             then
                                               let uu____28452 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____28461 =
                                                          let uu____28463 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____28463
                                                           in
                                                        Prims.op_Hat s
                                                          uu____28461) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____28452
                                             else ());
                                            (let wl4 =
                                               let uu___3708_28471 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3708_28471.attempting);
                                                 wl_deferred =
                                                   (uu___3708_28471.wl_deferred);
                                                 wl_deferred_to_tac =
                                                   (uu___3708_28471.wl_deferred_to_tac);
                                                 ctr = (uu___3708_28471.ctr);
                                                 defer_ok =
                                                   (uu___3708_28471.defer_ok);
                                                 smt_ok =
                                                   (uu___3708_28471.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3708_28471.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3708_28471.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits);
                                                 repr_subcomp_allowed =
                                                   (uu___3708_28471.repr_subcomp_allowed)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____28496 =
                                                        let uu____28503 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____28503, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____28496) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____28520 =
                                               let f_sort_is =
                                                 let uu____28530 =
                                                   let uu____28531 =
                                                     let uu____28534 =
                                                       let uu____28535 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28535.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28534
                                                      in
                                                   uu____28531.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28530 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28546,uu____28547::is)
                                                     ->
                                                     let uu____28589 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28589
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28622 ->
                                                     let uu____28623 =
                                                       let uu____28629 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28629)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28623 r
                                                  in
                                               let uu____28635 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28670  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28670
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28691 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28691
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28635
                                                in
                                             match uu____28520 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28716 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28716
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28717 =
                                                   let g_sort_is =
                                                     let uu____28727 =
                                                       let uu____28728 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28728.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28727 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28733,uu____28734::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28794 ->
                                                         let uu____28795 =
                                                           let uu____28801 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28801)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28795 r
                                                      in
                                                   let uu____28807 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28842  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28842
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28863
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28863
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28807
                                                    in
                                                 (match uu____28717 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28890 =
                                                          let uu____28895 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28896 =
                                                            let uu____28897 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28897
                                                             in
                                                          (uu____28895,
                                                            uu____28896)
                                                           in
                                                        match uu____28890
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28925 =
                                                          let uu____28928 =
                                                            let uu____28931 =
                                                              let uu____28934
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28934
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28931
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28928
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28925
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28958 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28958
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
                                                        let uu____28969 =
                                                          let uu____28972 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun uu____28975 
                                                               ->
                                                               FStar_Pervasives_Native.Some
                                                                 uu____28975)
                                                            uu____28972
                                                           in
                                                        solve_prob orig
                                                          uu____28969 [] wl6
                                                         in
                                                      let uu____28976 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28976))))))))))
           in
        let solve_sub c11 edge c21 =
          if
            problem.FStar_TypeChecker_Common.relation <>
              FStar_TypeChecker_Common.SUB
          then failwith "impossible: solve_sub"
          else ();
          (let r = FStar_TypeChecker_Env.get_range env  in
           let lift_c1 uu____29004 =
             let univs =
               match c11.FStar_Syntax_Syntax.comp_univs with
               | [] ->
                   let uu____29006 =
                     env.FStar_TypeChecker_Env.universe_of env
                       c11.FStar_Syntax_Syntax.result_typ
                      in
                   [uu____29006]
               | x -> x  in
             let c12 =
               let uu___3776_29009 = c11  in
               {
                 FStar_Syntax_Syntax.comp_univs = univs;
                 FStar_Syntax_Syntax.effect_name =
                   (uu___3776_29009.FStar_Syntax_Syntax.effect_name);
                 FStar_Syntax_Syntax.result_typ =
                   (uu___3776_29009.FStar_Syntax_Syntax.result_typ);
                 FStar_Syntax_Syntax.effect_args =
                   (uu___3776_29009.FStar_Syntax_Syntax.effect_args);
                 FStar_Syntax_Syntax.flags =
                   (uu___3776_29009.FStar_Syntax_Syntax.flags)
               }  in
             let uu____29010 =
               let uu____29015 =
                 FStar_All.pipe_right
                   (let uu___3779_29017 = c12  in
                    {
                      FStar_Syntax_Syntax.comp_univs = univs;
                      FStar_Syntax_Syntax.effect_name =
                        (uu___3779_29017.FStar_Syntax_Syntax.effect_name);
                      FStar_Syntax_Syntax.result_typ =
                        (uu___3779_29017.FStar_Syntax_Syntax.result_typ);
                      FStar_Syntax_Syntax.effect_args =
                        (uu___3779_29017.FStar_Syntax_Syntax.effect_args);
                      FStar_Syntax_Syntax.flags =
                        (uu___3779_29017.FStar_Syntax_Syntax.flags)
                    }) FStar_Syntax_Syntax.mk_Comp
                  in
               FStar_All.pipe_right uu____29015
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____29010
               (fun uu____29031  ->
                  match uu____29031 with
                  | (c,g) ->
                      let uu____29038 =
                        let uu____29040 = FStar_TypeChecker_Env.is_trivial g
                           in
                        Prims.op_Negation uu____29040  in
                      if uu____29038
                      then
                        let uu____29043 =
                          let uu____29049 =
                            let uu____29051 =
                              FStar_Ident.string_of_lid
                                c12.FStar_Syntax_Syntax.effect_name
                               in
                            let uu____29053 =
                              FStar_Ident.string_of_lid
                                c21.FStar_Syntax_Syntax.effect_name
                               in
                            FStar_Util.format2
                              "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                              uu____29051 uu____29053
                             in
                          (FStar_Errors.Fatal_UnexpectedEffect, uu____29049)
                           in
                        FStar_Errors.raise_error uu____29043 r
                      else FStar_Syntax_Util.comp_to_comp_typ c)
              in
           let uu____29059 =
             FStar_TypeChecker_Env.is_layered_effect env
               c21.FStar_Syntax_Syntax.effect_name
              in
           if uu____29059
           then solve_layered_sub c11 edge c21
           else
             (let uu____29064 =
                ((Prims.op_Negation wl.repr_subcomp_allowed) &&
                   (let uu____29067 =
                      FStar_Ident.lid_equals
                        c11.FStar_Syntax_Syntax.effect_name
                        c21.FStar_Syntax_Syntax.effect_name
                       in
                    Prims.op_Negation uu____29067))
                  &&
                  (FStar_TypeChecker_Env.is_reifiable_effect env
                     c21.FStar_Syntax_Syntax.effect_name)
                 in
              if uu____29064
              then
                let uu____29070 =
                  mklstr
                    (fun uu____29077  ->
                       let uu____29078 =
                         FStar_Ident.string_of_lid
                           c11.FStar_Syntax_Syntax.effect_name
                          in
                       let uu____29080 =
                         FStar_Ident.string_of_lid
                           c21.FStar_Syntax_Syntax.effect_name
                          in
                       FStar_Util.format2
                         "Cannot lift from %s to %s, it needs a lift\n"
                         uu____29078 uu____29080)
                   in
                giveup env uu____29070 orig
              else
                (let is_null_wp_2 =
                   FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                     (FStar_Util.for_some
                        (fun uu___28_29091  ->
                           match uu___28_29091 with
                           | FStar_Syntax_Syntax.TOTAL  -> true
                           | FStar_Syntax_Syntax.MLEFFECT  -> true
                           | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                           | uu____29096 -> false))
                    in
                 let uu____29098 =
                   match ((c11.FStar_Syntax_Syntax.effect_args),
                           (c21.FStar_Syntax_Syntax.effect_args))
                   with
                   | ((wp1,uu____29128)::uu____29129,(wp2,uu____29131)::uu____29132)
                       -> (wp1, wp2)
                   | uu____29205 ->
                       let uu____29230 =
                         let uu____29236 =
                           let uu____29238 =
                             FStar_Syntax_Print.lid_to_string
                               c11.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____29240 =
                             FStar_Syntax_Print.lid_to_string
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Got effects %s and %s, expected normalized effects"
                             uu____29238 uu____29240
                            in
                         (FStar_Errors.Fatal_ExpectNormalizedEffect,
                           uu____29236)
                          in
                       FStar_Errors.raise_error uu____29230
                         env.FStar_TypeChecker_Env.range
                    in
                 match uu____29098 with
                 | (wpc1,wpc2) ->
                     let uu____29250 = FStar_Util.physical_equality wpc1 wpc2
                        in
                     if uu____29250
                     then
                       let uu____29253 =
                         problem_using_guard orig
                           c11.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29253 wl
                     else
                       (let uu____29257 =
                          let uu____29264 =
                            FStar_TypeChecker_Env.effect_decl_opt env
                              c21.FStar_Syntax_Syntax.effect_name
                             in
                          FStar_Util.must uu____29264  in
                        match uu____29257 with
                        | (c2_decl,qualifiers) ->
                            let uu____29285 =
                              FStar_All.pipe_right qualifiers
                                (FStar_List.contains
                                   FStar_Syntax_Syntax.Reifiable)
                               in
                            if uu____29285
                            then
                              let c1_repr =
                                let uu____29292 =
                                  let uu____29293 =
                                    let uu____29294 = lift_c1 ()  in
                                    FStar_Syntax_Syntax.mk_Comp uu____29294
                                     in
                                  let uu____29295 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c11.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____29293 uu____29295
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.4"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____29292
                                 in
                              let c2_repr =
                                let uu____29298 =
                                  let uu____29299 =
                                    FStar_Syntax_Syntax.mk_Comp c21  in
                                  let uu____29300 =
                                    env.FStar_TypeChecker_Env.universe_of env
                                      c21.FStar_Syntax_Syntax.result_typ
                                     in
                                  FStar_TypeChecker_Env.reify_comp env
                                    uu____29299 uu____29300
                                   in
                                norm_with_steps
                                  "FStar.TypeChecker.Rel.norm_with_steps.5"
                                  [FStar_TypeChecker_Env.UnfoldUntil
                                     FStar_Syntax_Syntax.delta_constant;
                                  FStar_TypeChecker_Env.Weak;
                                  FStar_TypeChecker_Env.HNF] env uu____29298
                                 in
                              let uu____29302 =
                                let uu____29307 =
                                  let uu____29309 =
                                    FStar_Syntax_Print.term_to_string c1_repr
                                     in
                                  let uu____29311 =
                                    FStar_Syntax_Print.term_to_string c2_repr
                                     in
                                  FStar_Util.format2
                                    "sub effect repr: %s <: %s" uu____29309
                                    uu____29311
                                   in
                                sub_prob wl c1_repr
                                  problem.FStar_TypeChecker_Common.relation
                                  c2_repr uu____29307
                                 in
                              (match uu____29302 with
                               | (prob,wl1) ->
                                   let wl2 =
                                     solve_prob orig
                                       (FStar_Pervasives_Native.Some
                                          (p_guard prob)) [] wl1
                                      in
                                   let uu____29317 = attempt [prob] wl2  in
                                   solve env uu____29317)
                            else
                              (let g =
                                 if env.FStar_TypeChecker_Env.lax
                                 then FStar_Syntax_Util.t_true
                                 else
                                   (let wpc1_2 =
                                      let uu____29337 = lift_c1 ()  in
                                      FStar_All.pipe_right uu____29337
                                        (fun ct  ->
                                           FStar_List.hd
                                             ct.FStar_Syntax_Syntax.effect_args)
                                       in
                                    if is_null_wp_2
                                    then
                                      ((let uu____29360 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other "Rel")
                                           in
                                        if uu____29360
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
                                          let uu____29370 =
                                            FStar_All.pipe_right c2_decl
                                              FStar_Syntax_Util.get_wp_trivial_combinator
                                             in
                                          match uu____29370 with
                                          | FStar_Pervasives_Native.None  ->
                                              failwith
                                                "Rel doesn't yet handle undefined trivial combinator in an effect"
                                          | FStar_Pervasives_Native.Some t ->
                                              t
                                           in
                                        let uu____29377 =
                                          let uu____29378 =
                                            let uu____29395 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____29398 =
                                              let uu____29409 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____29409; wpc1_2]  in
                                            (uu____29395, uu____29398)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____29378
                                           in
                                        FStar_Syntax_Syntax.mk uu____29377 r))
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
                                       let uu____29458 =
                                         let uu____29459 =
                                           let uu____29476 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____29479 =
                                             let uu____29490 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____29499 =
                                               let uu____29510 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____29510; wpc1_2]  in
                                             uu____29490 :: uu____29499  in
                                           (uu____29476, uu____29479)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____29459
                                          in
                                       FStar_Syntax_Syntax.mk uu____29458 r))
                                  in
                               (let uu____29564 =
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.debug env)
                                    (FStar_Options.Other "Rel")
                                   in
                                if uu____29564
                                then
                                  let uu____29569 =
                                    let uu____29571 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Iota;
                                        FStar_TypeChecker_Env.Eager_unfolding;
                                        FStar_TypeChecker_Env.Primops;
                                        FStar_TypeChecker_Env.Simplify] env g
                                       in
                                    FStar_Syntax_Print.term_to_string
                                      uu____29571
                                     in
                                  FStar_Util.print1
                                    "WP guard (simplifed) is (%s)\n"
                                    uu____29569
                                else ());
                               (let uu____29575 =
                                  sub_prob wl
                                    c11.FStar_Syntax_Syntax.result_typ
                                    problem.FStar_TypeChecker_Common.relation
                                    c21.FStar_Syntax_Syntax.result_typ
                                    "result type"
                                   in
                                match uu____29575 with
                                | (base_prob,wl1) ->
                                    let wl2 =
                                      let uu____29584 =
                                        let uu____29587 =
                                          FStar_Syntax_Util.mk_conj
                                            (p_guard base_prob) g
                                           in
                                        FStar_All.pipe_left
                                          (fun uu____29590  ->
                                             FStar_Pervasives_Native.Some
                                               uu____29590) uu____29587
                                         in
                                      solve_prob orig uu____29584 [] wl1  in
                                    let uu____29591 = attempt [base_prob] wl2
                                       in
                                    solve env uu____29591))))))
           in
        let uu____29592 = FStar_Util.physical_equality c1 c2  in
        if uu____29592
        then
          let uu____29595 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29595
        else
          ((let uu____29599 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29599
            then
              let uu____29604 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29606 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29604
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29606
            else ());
           (let uu____29611 =
              let uu____29620 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29623 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29620, uu____29623)  in
            match uu____29611 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29641),FStar_Syntax_Syntax.Total
                    (t2,uu____29643)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29660 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29660 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29662,FStar_Syntax_Syntax.Total uu____29663) ->
                     let uu____29680 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29680 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29684),FStar_Syntax_Syntax.Total
                    (t2,uu____29686)) ->
                     let uu____29703 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29703 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29706),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29708)) ->
                     let uu____29725 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29725 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29728),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29730)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29747 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29747 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29750),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29752)) ->
                     let uu____29769 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29769 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29772,FStar_Syntax_Syntax.Comp uu____29773) ->
                     let uu____29782 =
                       let uu___3904_29785 = problem  in
                       let uu____29788 =
                         let uu____29789 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29789
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3904_29785.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29788;
                         FStar_TypeChecker_Common.relation =
                           (uu___3904_29785.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3904_29785.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3904_29785.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3904_29785.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3904_29785.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3904_29785.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3904_29785.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3904_29785.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29782 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29790,FStar_Syntax_Syntax.Comp uu____29791) ->
                     let uu____29800 =
                       let uu___3904_29803 = problem  in
                       let uu____29806 =
                         let uu____29807 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29807
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3904_29803.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29806;
                         FStar_TypeChecker_Common.relation =
                           (uu___3904_29803.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3904_29803.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3904_29803.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3904_29803.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3904_29803.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3904_29803.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3904_29803.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3904_29803.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29800 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29808,FStar_Syntax_Syntax.GTotal uu____29809) ->
                     let uu____29818 =
                       let uu___3916_29821 = problem  in
                       let uu____29824 =
                         let uu____29825 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29825
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3916_29821.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3916_29821.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3916_29821.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29824;
                         FStar_TypeChecker_Common.element =
                           (uu___3916_29821.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3916_29821.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3916_29821.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3916_29821.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3916_29821.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3916_29821.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29818 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29826,FStar_Syntax_Syntax.Total uu____29827) ->
                     let uu____29836 =
                       let uu___3916_29839 = problem  in
                       let uu____29842 =
                         let uu____29843 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29843
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3916_29839.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3916_29839.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3916_29839.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29842;
                         FStar_TypeChecker_Common.element =
                           (uu___3916_29839.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3916_29839.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3916_29839.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3916_29839.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3916_29839.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3916_29839.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29836 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29844,FStar_Syntax_Syntax.Comp uu____29845) ->
                     let uu____29846 =
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
                     if uu____29846
                     then
                       let uu____29849 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29849 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29856 =
                            let uu____29861 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29861
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29870 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29871 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29870, uu____29871))
                             in
                          match uu____29856 with
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
                           (let uu____29879 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29879
                            then
                              let uu____29884 =
                                FStar_Ident.string_of_lid
                                  c12.FStar_Syntax_Syntax.effect_name
                                 in
                              let uu____29886 =
                                FStar_Ident.string_of_lid
                                  c22.FStar_Syntax_Syntax.effect_name
                                 in
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                uu____29884 uu____29886
                            else ());
                           (let uu____29891 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29891 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29894 =
                                  mklstr
                                    (fun uu____29901  ->
                                       let uu____29902 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29904 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29902 uu____29904)
                                   in
                                giveup env uu____29894 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29915 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29915 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29965 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29965 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29990 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____30021  ->
                match uu____30021 with
                | (u1,u2) ->
                    let uu____30029 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____30031 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____30029 uu____30031))
         in
      FStar_All.pipe_right uu____29990 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____30068,[])) when
          let uu____30095 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____30095 -> "{}"
      | uu____30098 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____30125 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____30125
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry defs =
            let uu____30156 =
              FStar_List.map
                (fun uu____30170  ->
                   match uu____30170 with
                   | (msg,x) ->
                       let uu____30181 =
                         let uu____30183 = prob_to_string env x  in
                         Prims.op_Hat ": " uu____30183  in
                       Prims.op_Hat msg uu____30181) defs
               in
            FStar_All.pipe_right uu____30156 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30193 = carry g.FStar_TypeChecker_Common.deferred  in
          let uu____30195 = carry g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____30197 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30193 uu____30195 uu____30197 imps
  
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
                  let uu____30254 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30254
                  then
                    let uu____30262 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30264 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30262
                      (rel_to_string rel) uu____30264
                  else "TOP"  in
                let uu____30270 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30270 with
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
              let uu____30330 =
                let uu____30333 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun uu____30336  ->
                     FStar_Pervasives_Native.Some uu____30336) uu____30333
                 in
              FStar_Syntax_Syntax.new_bv uu____30330 t1  in
            let uu____30337 =
              let uu____30342 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30342
               in
            match uu____30337 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____30414 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30414
         then
           let uu____30419 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30419
         else ());
        (let uu____30426 =
           FStar_Util.record_time (fun uu____30433  -> solve env probs)  in
         match uu____30426 with
         | (sol,ms) ->
             ((let uu____30447 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30447
               then
                 let uu____30452 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30452
               else ());
              (match sol with
               | Success (deferred,defer_to_tac,implicits) ->
                   let uu____30468 =
                     FStar_Util.record_time
                       (fun uu____30475  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30468 with
                    | ((),ms1) ->
                        ((let uu____30488 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30488
                          then
                            let uu____30493 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30493
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d,s) ->
                   ((let uu____30507 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30507
                     then
                       let uu____30514 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30514
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
          ((let uu____30542 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30542
            then
              let uu____30547 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30547
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30555 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30555
             then
               let uu____30560 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30560
             else ());
            (let f2 =
               let uu____30566 =
                 let uu____30567 = FStar_Syntax_Util.unmeta f1  in
                 uu____30567.FStar_Syntax_Syntax.n  in
               match uu____30566 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30571 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4035_30572 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4035_30572.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4035_30572.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4035_30572.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4035_30572.FStar_TypeChecker_Common.implicits)
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
            let uu____30624 =
              let uu____30625 =
                let uu____30626 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun uu____30627  ->
                       FStar_TypeChecker_Common.NonTrivial uu____30627)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30626;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30625  in
            FStar_All.pipe_left
              (fun uu____30634  -> FStar_Pervasives_Native.Some uu____30634)
              uu____30624
  
let with_guard_no_simp :
  'uuuuuu30644 .
    'uuuuuu30644 ->
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
            let uu____30693 =
              let uu____30694 =
                FStar_All.pipe_right (p_guard prob)
                  (fun uu____30695  ->
                     FStar_TypeChecker_Common.NonTrivial uu____30695)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30694;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30693
  
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
          (let uu____30728 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30728
           then
             let uu____30733 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30735 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30733
               uu____30735
           else ());
          (let uu____30740 =
             let uu____30745 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30745
              in
           match uu____30740 with
           | (prob,wl) ->
               let g =
                 let uu____30753 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30763  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30753  in
               ((let uu____30785 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30785
                 then
                   let uu____30790 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30790
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
        let uu____30811 = try_teq true env t1 t2  in
        match uu____30811 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30816 = FStar_TypeChecker_Env.get_range env  in
              let uu____30817 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30816 uu____30817);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30825 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30825
              then
                let uu____30830 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30832 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30834 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30830
                  uu____30832 uu____30834
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
        (let uu____30858 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30858
         then
           let uu____30863 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30865 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30863
             uu____30865
         else ());
        (let uu____30870 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30870 with
         | (prob,x,wl) ->
             let g =
               let uu____30885 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30896  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30885  in
             ((let uu____30918 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30918
               then
                 let uu____30923 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30923
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30931 =
                     let uu____30932 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30932 g1  in
                   FStar_Pervasives_Native.Some uu____30931)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30954 = FStar_TypeChecker_Env.get_range env  in
          let uu____30955 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30954 uu____30955
  
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
        (let uu____30984 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30984
         then
           let uu____30989 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30991 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30989 uu____30991
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____31002 =
           let uu____31009 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____31009 "sub_comp"
            in
         match uu____31002 with
         | (prob,wl) ->
             let wl1 =
               let uu___4108_31020 = wl  in
               {
                 attempting = (uu___4108_31020.attempting);
                 wl_deferred = (uu___4108_31020.wl_deferred);
                 wl_deferred_to_tac = (uu___4108_31020.wl_deferred_to_tac);
                 ctr = (uu___4108_31020.ctr);
                 defer_ok = (uu___4108_31020.defer_ok);
                 smt_ok = (uu___4108_31020.smt_ok);
                 umax_heuristic_ok = (uu___4108_31020.umax_heuristic_ok);
                 tcenv = (uu___4108_31020.tcenv);
                 wl_implicits = (uu___4108_31020.wl_implicits);
                 repr_subcomp_allowed = true
               }  in
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____31025 =
                 FStar_Util.record_time
                   (fun uu____31037  ->
                      let uu____31038 =
                        solve_and_commit env (singleton wl1 prob1 true)
                          (fun uu____31049  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____31038)
                  in
               match uu____31025 with
               | (r,ms) ->
                   ((let uu____31081 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____31081
                     then
                       let uu____31086 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____31088 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____31090 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____31086 uu____31088
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____31090
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
      fun uu____31128  ->
        match uu____31128 with
        | (variables,ineqs) ->
            let fail u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31171 =
                 let uu____31177 =
                   let uu____31179 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31181 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31179 uu____31181
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31177)  in
               let uu____31185 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31171 uu____31185)
               in
            let equiv v v' =
              let uu____31198 =
                let uu____31203 = FStar_Syntax_Subst.compress_univ v  in
                let uu____31204 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31203, uu____31204)  in
              match uu____31198 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31228 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v  ->
                      let uu____31259 = FStar_Syntax_Subst.compress_univ v
                         in
                      match uu____31259 with
                      | FStar_Syntax_Syntax.U_unif uu____31266 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31297  ->
                                    match uu____31297 with
                                    | (u,v') ->
                                        let uu____31306 = equiv v v'  in
                                        if uu____31306
                                        then
                                          let uu____31311 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv u))
                                             in
                                          (if uu____31311 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v)]
                      | uu____31332 -> []))
               in
            let uu____31337 =
              let wl =
                let uu___4151_31341 = empty_worklist env  in
                {
                  attempting = (uu___4151_31341.attempting);
                  wl_deferred = (uu___4151_31341.wl_deferred);
                  wl_deferred_to_tac = (uu___4151_31341.wl_deferred_to_tac);
                  ctr = (uu___4151_31341.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4151_31341.smt_ok);
                  umax_heuristic_ok = (uu___4151_31341.umax_heuristic_ok);
                  tcenv = (uu___4151_31341.tcenv);
                  wl_implicits = (uu___4151_31341.wl_implicits);
                  repr_subcomp_allowed =
                    (uu___4151_31341.repr_subcomp_allowed)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31360  ->
                      match uu____31360 with
                      | (lb,v) ->
                          let uu____31367 =
                            solve_universe_eq (~- Prims.int_one) wl lb v  in
                          (match uu____31367 with
                           | USolved wl1 -> ()
                           | uu____31370 -> fail lb v)))
               in
            let rec check_ineq uu____31381 =
              match uu____31381 with
              | (u,v) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v1 =
                    FStar_TypeChecker_Normalize.normalize_universe env v  in
                  (match (u1, v1) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31393) -> true
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
                      uu____31421,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31423,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31436) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v1)))
                   | (uu____31444,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v2  -> check_ineq (u1, v2)))
                   | uu____31453 -> false)
               in
            let uu____31459 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31476  ->
                      match uu____31476 with
                      | (u,v) ->
                          let uu____31484 = check_ineq (u, v)  in
                          if uu____31484
                          then true
                          else
                            ((let uu____31492 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31492
                              then
                                let uu____31497 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31499 =
                                  FStar_Syntax_Print.univ_to_string v  in
                                FStar_Util.print2 "%s </= %s" uu____31497
                                  uu____31499
                              else ());
                             false)))
               in
            if uu____31459
            then ()
            else
              ((let uu____31509 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31509
                then
                  ((let uu____31515 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31515);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31527 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31527))
                else ());
               (let uu____31540 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31540))
  
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
          let fail uu____31622 =
            match uu____31622 with
            | (d,s) ->
                let msg = explain env d s  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                  (p_loc d)
             in
          let wl =
            let uu___4229_31649 =
              wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
            {
              attempting = (uu___4229_31649.attempting);
              wl_deferred = (uu___4229_31649.wl_deferred);
              wl_deferred_to_tac = (uu___4229_31649.wl_deferred_to_tac);
              ctr = (uu___4229_31649.ctr);
              defer_ok;
              smt_ok;
              umax_heuristic_ok = (uu___4229_31649.umax_heuristic_ok);
              tcenv = (uu___4229_31649.tcenv);
              wl_implicits = (uu___4229_31649.wl_implicits);
              repr_subcomp_allowed = (uu___4229_31649.repr_subcomp_allowed)
            }  in
          (let uu____31652 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____31652
           then
             let uu____31657 = FStar_Util.string_of_bool defer_ok  in
             let uu____31659 = wl_to_string wl  in
             let uu____31661 =
               FStar_Util.string_of_int
                 (FStar_List.length g.FStar_TypeChecker_Common.implicits)
                in
             FStar_Util.print3
               "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
               uu____31657 uu____31659 uu____31661
           else ());
          (let g1 =
             let uu____31667 = solve_and_commit env wl fail  in
             match uu____31667 with
             | FStar_Pervasives_Native.Some
                 (uu____31676::uu____31677,uu____31678,uu____31679) when
                 Prims.op_Negation defer_ok ->
                 failwith
                   "Impossible: Unexpected deferred constraints remain"
             | FStar_Pervasives_Native.Some (deferred,defer_to_tac,imps) ->
                 let uu___4246_31713 = g  in
                 {
                   FStar_TypeChecker_Common.guard_f =
                     (uu___4246_31713.FStar_TypeChecker_Common.guard_f);
                   FStar_TypeChecker_Common.deferred_to_tac =
                     (FStar_List.append
                        g.FStar_TypeChecker_Common.deferred_to_tac
                        defer_to_tac);
                   FStar_TypeChecker_Common.deferred = deferred;
                   FStar_TypeChecker_Common.univ_ineqs =
                     (uu___4246_31713.FStar_TypeChecker_Common.univ_ineqs);
                   FStar_TypeChecker_Common.implicits =
                     (FStar_List.append g.FStar_TypeChecker_Common.implicits
                        imps)
                 }
             | uu____31719 ->
                 failwith "Impossible: should have raised a failure already"
              in
           solve_universe_inequalities env
             g1.FStar_TypeChecker_Common.univ_ineqs;
           (let uu___4251_31730 = g1  in
            {
              FStar_TypeChecker_Common.guard_f =
                (uu___4251_31730.FStar_TypeChecker_Common.guard_f);
              FStar_TypeChecker_Common.deferred_to_tac =
                (uu___4251_31730.FStar_TypeChecker_Common.deferred_to_tac);
              FStar_TypeChecker_Common.deferred =
                (uu___4251_31730.FStar_TypeChecker_Common.deferred);
              FStar_TypeChecker_Common.univ_ineqs = ([], []);
              FStar_TypeChecker_Common.implicits =
                (uu___4251_31730.FStar_TypeChecker_Common.implicits)
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
          (let uu____31826 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____31826
           then
             let uu____31831 = guard_to_string env g  in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31831
           else ());
          (let g1 = solve_deferred_constraints' use_smt env g  in
           let ret_g =
             let uu___4268_31838 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4268_31838.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4268_31838.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4268_31838.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4268_31838.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31839 =
             let uu____31841 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31841  in
           if uu____31839
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug
                   then
                     (let uu____31853 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31854 =
                        let uu____31856 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31856
                         in
                      FStar_Errors.diag uu____31853 uu____31854)
                   else ();
                   (let vc1 =
                      let uu____31862 =
                        let uu____31866 =
                          let uu____31868 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31868  in
                        FStar_Pervasives_Native.Some uu____31866  in
                      FStar_Profiling.profile
                        (fun uu____31871  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31862 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug
                    then
                      (let uu____31875 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31876 =
                         let uu____31878 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31878
                          in
                       FStar_Errors.diag uu____31875 uu____31876)
                    else ();
                    (let uu____31884 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31884 "discharge_guard'" env vc1);
                    (let uu____31886 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31886 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug
                            then
                              (let uu____31895 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31896 =
                                 let uu____31898 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31898
                                  in
                               FStar_Errors.diag uu____31895 uu____31896)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug
                            then
                              (let uu____31908 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31909 =
                                 let uu____31911 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31911
                                  in
                               FStar_Errors.diag uu____31908 uu____31909)
                            else ();
                            (let vcs =
                               let uu____31925 = FStar_Options.use_tactics ()
                                  in
                               if uu____31925
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31947  ->
                                      (let uu____31949 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left
                                         (fun uu____31951  -> ()) uu____31949);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31994  ->
                                               match uu____31994 with
                                               | (env1,goal,opts) ->
                                                   let uu____32010 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____32010, opts)))))
                               else
                                 (let uu____32014 =
                                    let uu____32021 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____32021)  in
                                  [uu____32014])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____32054  ->
                                     match uu____32054 with
                                     | (env1,goal,opts) ->
                                         let uu____32064 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____32064 with
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
                                                 (let uu____32075 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____32076 =
                                                    let uu____32078 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____32080 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____32078 uu____32080
                                                     in
                                                  FStar_Errors.diag
                                                    uu____32075 uu____32076)
                                               else ();
                                               if debug
                                               then
                                                 (let uu____32087 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____32088 =
                                                    let uu____32090 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____32090
                                                     in
                                                  FStar_Errors.diag
                                                    uu____32087 uu____32088)
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
      let uu____32108 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____32108 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____32117 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____32117
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____32131 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____32131 with
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
        let uu____32161 = try_teq false env t1 t2  in
        match uu____32161 with
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
            let uu____32205 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32205 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32212 ->
                     let uu____32213 =
                       let uu____32214 = FStar_Syntax_Subst.compress r  in
                       uu____32214.FStar_Syntax_Syntax.n  in
                     (match uu____32213 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32219) ->
                          unresolved ctx_u'
                      | uu____32236 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32260 = acc  in
            match uu____32260 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd::tl ->
                     let uu____32279 = hd  in
                     (match uu____32279 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl
                          else
                            (let uu____32290 = unresolved ctx_u  in
                             if uu____32290
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32301 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32301
                                     then
                                       let uu____32305 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32305
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32314 = teq_nosmt env1 t tm
                                          in
                                       match uu____32314 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4381_32324 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4381_32324.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4381_32324.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4381_32324.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4381_32324.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4381_32324.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4381_32324.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4381_32324.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd1 =
                                       let uu___4384_32326 = hd  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4384_32326.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4384_32326.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4384_32326.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl)))
                               | uu____32329 ->
                                   until_fixpoint ((hd :: out), changed) tl
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl
                               else
                                 (let env1 =
                                    let uu___4389_32341 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4389_32341.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4389_32341.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4389_32341.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4389_32341.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4389_32341.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4389_32341.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4389_32341.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4389_32341.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4389_32341.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4389_32341.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4389_32341.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4389_32341.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4389_32341.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4389_32341.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4389_32341.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4389_32341.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4389_32341.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4389_32341.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4389_32341.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4389_32341.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4389_32341.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4389_32341.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4389_32341.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4389_32341.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4389_32341.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4389_32341.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4389_32341.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4389_32341.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4389_32341.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4389_32341.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4389_32341.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4389_32341.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4389_32341.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4389_32341.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4389_32341.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4389_32341.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4389_32341.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4389_32341.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4389_32341.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4389_32341.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4389_32341.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4389_32341.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4389_32341.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4389_32341.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4389_32341.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___4389_32341.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4394_32346 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4394_32346.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4394_32346.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4394_32346.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4394_32346.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4394_32346.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4394_32346.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4394_32346.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4394_32346.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4394_32346.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4394_32346.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4394_32346.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4394_32346.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4394_32346.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4394_32346.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4394_32346.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4394_32346.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4394_32346.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4394_32346.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4394_32346.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4394_32346.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4394_32346.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4394_32346.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4394_32346.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4394_32346.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4394_32346.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4394_32346.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4394_32346.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4394_32346.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4394_32346.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4394_32346.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4394_32346.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4394_32346.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4394_32346.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4394_32346.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4394_32346.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4394_32346.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4394_32346.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4394_32346.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4394_32346.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4394_32346.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4394_32346.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4394_32346.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4394_32346.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4394_32346.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4394_32346.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4394_32346.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      }
                                    else env1  in
                                  (let uu____32351 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32351
                                   then
                                     let uu____32356 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32358 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32360 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32362 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32356 uu____32358 uu____32360
                                       reason uu____32362
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4400_32369  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32376 =
                                             let uu____32386 =
                                               let uu____32394 =
                                                 let uu____32396 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32398 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32400 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32396 uu____32398
                                                   uu____32400
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32394, r)
                                                in
                                             [uu____32386]  in
                                           FStar_Errors.add_errors
                                             uu____32376);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32419 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32430  ->
                                               let uu____32431 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32433 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32435 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32431 uu____32433
                                                 reason uu____32435)) env2 g1
                                         true
                                        in
                                     match uu____32419 with
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
          let uu___4412_32443 = g  in
          let uu____32444 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4412_32443.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4412_32443.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4412_32443.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4412_32443.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32444
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____32459 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32459
       then
         let uu____32464 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32464
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
      (let uu____32495 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32495
       then
         let uu____32500 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32500
       else ());
      (let solve_goals_with_tac imps tac =
         let deferred_goals =
           FStar_TypeChecker_DeferredImplicits.sort_goals env imps  in
         let guard =
           let uu___4428_32518 = g  in
           {
             FStar_TypeChecker_Common.guard_f =
               (uu___4428_32518.FStar_TypeChecker_Common.guard_f);
             FStar_TypeChecker_Common.deferred_to_tac = [];
             FStar_TypeChecker_Common.deferred =
               (uu___4428_32518.FStar_TypeChecker_Common.deferred);
             FStar_TypeChecker_Common.univ_ineqs =
               (uu___4428_32518.FStar_TypeChecker_Common.univ_ineqs);
             FStar_TypeChecker_Common.implicits = imps
           }  in
         let resolve_tac =
           match tac.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_let (uu____32525,lid::[]) ->
               let qn = FStar_TypeChecker_Env.lookup_qname env lid  in
               let fv =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   (FStar_Syntax_Syntax.Delta_constant_at_level
                      Prims.int_zero) FStar_Pervasives_Native.None
                  in
               let dd =
                 let uu____32533 =
                   FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn  in
                 match uu____32533 with
                 | FStar_Pervasives_Native.Some dd -> dd
                 | FStar_Pervasives_Native.None  -> failwith "Expected a dd"
                  in
               let term =
                 let uu____32539 =
                   FStar_Syntax_Syntax.lid_as_fv lid dd
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____32539  in
               term
           | uu____32540 -> failwith "Resolve_tac not found"  in
         let env1 =
           let uu___4445_32543 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___4445_32543.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___4445_32543.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___4445_32543.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___4445_32543.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___4445_32543.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___4445_32543.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___4445_32543.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___4445_32543.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___4445_32543.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___4445_32543.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___4445_32543.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___4445_32543.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___4445_32543.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___4445_32543.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___4445_32543.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___4445_32543.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___4445_32543.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___4445_32543.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___4445_32543.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___4445_32543.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___4445_32543.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___4445_32543.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___4445_32543.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___4445_32543.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___4445_32543.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___4445_32543.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___4445_32543.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___4445_32543.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___4445_32543.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___4445_32543.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___4445_32543.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___4445_32543.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___4445_32543.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___4445_32543.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___4445_32543.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___4445_32543.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___4445_32543.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___4445_32543.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___4445_32543.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___4445_32543.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___4445_32543.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___4445_32543.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___4445_32543.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___4445_32543.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___4445_32543.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___4445_32543.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac = false
           }  in
         env1.FStar_TypeChecker_Env.try_solve_implicits_hook env1 resolve_tac
           deferred_goals
          in
       let solve_deferred_to_tactic g1 =
         let deferred = g1.FStar_TypeChecker_Common.deferred_to_tac  in
         match deferred with
         | [] -> g1
         | uu____32557 ->
             let prob_as_implicit uu____32572 =
               match uu____32572 with
               | (reason,prob) ->
                   (match prob with
                    | FStar_TypeChecker_Common.TProb tp when
                        tp.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ
                        ->
                        let env1 =
                          let uu___4459_32594 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4459_32594.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4459_32594.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4459_32594.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              ((tp.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4459_32594.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4459_32594.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4459_32594.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4459_32594.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4459_32594.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4459_32594.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4459_32594.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4459_32594.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4459_32594.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4459_32594.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4459_32594.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4459_32594.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4459_32594.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4459_32594.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4459_32594.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4459_32594.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___4459_32594.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4459_32594.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4459_32594.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4459_32594.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4459_32594.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4459_32594.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4459_32594.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4459_32594.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4459_32594.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4459_32594.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___4459_32594.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4459_32594.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4459_32594.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4459_32594.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4459_32594.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4459_32594.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4459_32594.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4459_32594.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4459_32594.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4459_32594.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4459_32594.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4459_32594.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4459_32594.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4459_32594.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4459_32594.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4459_32594.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4459_32594.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let env_lax =
                          let uu___4462_32596 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4462_32596.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4462_32596.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4462_32596.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___4462_32596.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4462_32596.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4462_32596.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4462_32596.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4462_32596.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4462_32596.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4462_32596.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4462_32596.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4462_32596.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4462_32596.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4462_32596.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4462_32596.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4462_32596.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4462_32596.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4462_32596.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4462_32596.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4462_32596.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4462_32596.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4462_32596.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4462_32596.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4462_32596.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4462_32596.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4462_32596.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4462_32596.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4462_32596.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4462_32596.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts = true;
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4462_32596.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4462_32596.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4462_32596.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4462_32596.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4462_32596.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4462_32596.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4462_32596.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4462_32596.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4462_32596.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4462_32596.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4462_32596.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4462_32596.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4462_32596.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4462_32596.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4462_32596.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4462_32596.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let uu____32599 =
                          env1.FStar_TypeChecker_Env.type_of env_lax
                            tp.FStar_TypeChecker_Common.lhs
                           in
                        (match uu____32599 with
                         | (uu____32610,tlhs,uu____32612) ->
                             let goal_ty =
                               let uu____32614 =
                                 env1.FStar_TypeChecker_Env.universe_of
                                   env_lax tlhs
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____32614 tlhs
                                 tp.FStar_TypeChecker_Common.lhs
                                 tp.FStar_TypeChecker_Common.rhs
                                in
                             let uu____32615 =
                               FStar_TypeChecker_Env.new_implicit_var_aux
                                 reason
                                 (tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos
                                 env1 goal_ty
                                 FStar_Syntax_Syntax.Allow_untyped
                                 FStar_Pervasives_Native.None
                                in
                             (match uu____32615 with
                              | (goal,ctx_uvar,uu____32634) ->
                                  let imp =
                                    let uu____32648 =
                                      let uu____32649 =
                                        FStar_List.hd ctx_uvar  in
                                      FStar_Pervasives_Native.fst uu____32649
                                       in
                                    {
                                      FStar_TypeChecker_Common.imp_reason =
                                        "";
                                      FStar_TypeChecker_Common.imp_uvar =
                                        uu____32648;
                                      FStar_TypeChecker_Common.imp_tm = goal;
                                      FStar_TypeChecker_Common.imp_range =
                                        ((tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos)
                                    }  in
                                  let sigelt =
                                    let uu____32662 =
                                      is_flex tp.FStar_TypeChecker_Common.lhs
                                       in
                                    if uu____32662
                                    then
                                      let uu____32667 =
                                        flex_uvar_head
                                          tp.FStar_TypeChecker_Common.lhs
                                         in
                                      find_user_tac_for_uvar env1 uu____32667
                                    else
                                      (let uu____32670 =
                                         is_flex
                                           tp.FStar_TypeChecker_Common.rhs
                                          in
                                       if uu____32670
                                       then
                                         let uu____32675 =
                                           flex_uvar_head
                                             tp.FStar_TypeChecker_Common.rhs
                                            in
                                         find_user_tac_for_uvar env1
                                           uu____32675
                                       else FStar_Pervasives_Native.None)
                                     in
                                  (match sigelt with
                                   | FStar_Pervasives_Native.None  ->
                                       failwith
                                         "Impossible: No tactic associated with deferred problem"
                                   | FStar_Pervasives_Native.Some se ->
                                       (imp, se))))
                    | uu____32688 ->
                        failwith "Unexpected problem deferred to tactic")
                in
             let eqs =
               FStar_List.map prob_as_implicit
                 g1.FStar_TypeChecker_Common.deferred_to_tac
                in
             let uu____32710 =
               FStar_List.fold_right
                 (fun imp  ->
                    fun uu____32742  ->
                      match uu____32742 with
                      | (more,imps) ->
                          let uu____32785 =
                            FStar_Syntax_Unionfind.find
                              (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          (match uu____32785 with
                           | FStar_Pervasives_Native.Some uu____32800 ->
                               (more, (imp :: imps))
                           | FStar_Pervasives_Native.None  ->
                               let se =
                                 find_user_tac_for_uvar env
                                   imp.FStar_TypeChecker_Common.imp_uvar
                                  in
                               (match se with
                                | FStar_Pervasives_Native.None  ->
                                    (more, (imp :: imps))
                                | FStar_Pervasives_Native.Some se1 ->
                                    let imp1 =
                                      match (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_meta
                                      with
                                      | FStar_Pervasives_Native.Some
                                          (FStar_Syntax_Syntax.Ctx_uvar_meta_attr
                                          a) ->
                                          let reason =
                                            let uu____32839 =
                                              FStar_Syntax_Print.term_to_string
                                                a
                                               in
                                            FStar_Util.format2 "%s::%s"
                                              uu____32839
                                              imp.FStar_TypeChecker_Common.imp_reason
                                             in
                                          let uu___4498_32842 = imp  in
                                          {
                                            FStar_TypeChecker_Common.imp_reason
                                              = reason;
                                            FStar_TypeChecker_Common.imp_uvar
                                              =
                                              (uu___4498_32842.FStar_TypeChecker_Common.imp_uvar);
                                            FStar_TypeChecker_Common.imp_tm =
                                              (uu___4498_32842.FStar_TypeChecker_Common.imp_tm);
                                            FStar_TypeChecker_Common.imp_range
                                              =
                                              (uu___4498_32842.FStar_TypeChecker_Common.imp_range)
                                          }
                                      | uu____32843 -> imp  in
                                    (((imp1, se1) :: more), imps))))
                 g1.FStar_TypeChecker_Common.implicits ([], [])
                in
             (match uu____32710 with
              | (more,imps) ->
                  let bucketize is =
                    let map = FStar_Util.smap_create (Prims.of_int (17))  in
                    FStar_List.iter
                      (fun uu____32939  ->
                         match uu____32939 with
                         | (i,s) ->
                             let uu____32946 =
                               FStar_Syntax_Util.lid_of_sigelt s  in
                             (match uu____32946 with
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Unexpected: tactic without a name"
                              | FStar_Pervasives_Native.Some l ->
                                  let lstr = FStar_Ident.string_of_lid l  in
                                  let uu____32953 =
                                    FStar_Util.smap_try_find map lstr  in
                                  (match uu____32953 with
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Util.smap_add map lstr ([i], s)
                                   | FStar_Pervasives_Native.Some (is1,s1) ->
                                       (FStar_Util.smap_remove map lstr;
                                        FStar_Util.smap_add map lstr
                                          ((i :: is1), s1))))) is;
                    FStar_Util.smap_fold map
                      (fun uu____33000  -> fun is1  -> fun out  -> is1 :: out)
                      []
                     in
                  let buckets = bucketize (FStar_List.append eqs more)  in
                  (FStar_List.iter
                     (fun uu____33041  ->
                        match uu____33041 with
                        | (imps1,sigel) -> solve_goals_with_tac imps1 sigel)
                     buckets;
                   (let uu___4530_33048 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___4530_33048.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac = [];
                      FStar_TypeChecker_Common.deferred =
                        (uu___4530_33048.FStar_TypeChecker_Common.deferred);
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___4530_33048.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits = imps
                    })))
          in
       let g1 = solve_deferred_constraints env g  in
       let g2 = solve_deferred_to_tactic g1  in
       (let uu____33057 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ResolveImplicitsHook")
           in
        if uu____33057
        then
          let uu____33062 = guard_to_string env g2  in
          FStar_Util.print1
            "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
            uu____33062
        else ());
       (let g3 = resolve_implicits env g2  in
        match g3.FStar_TypeChecker_Common.implicits with
        | [] ->
            let uu____33068 = discharge_guard env g3  in
            FStar_All.pipe_left (fun uu____33069  -> ()) uu____33068
        | imp::uu____33071 ->
            let uu____33074 =
              let uu____33080 =
                let uu____33082 =
                  FStar_Syntax_Print.uvar_to_string
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                   in
                let uu____33084 =
                  FStar_TypeChecker_Normalize.term_to_string env
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                   in
                FStar_Util.format3
                  "Failed to resolve implicit argument %s of type %s introduced for %s"
                  uu____33082 uu____33084
                  imp.FStar_TypeChecker_Common.imp_reason
                 in
              (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____33080)
               in
            FStar_Errors.raise_error uu____33074
              imp.FStar_TypeChecker_Common.imp_range))
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33104 = teq env t1 t2  in
        force_trivial_guard env uu____33104
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33123 = teq_nosmt env t1 t2  in
        match uu____33123 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4553_33142 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4553_33142.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4553_33142.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4553_33142.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4553_33142.FStar_TypeChecker_Common.implicits)
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
        (let uu____33178 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____33178
         then
           let uu____33183 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____33185 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____33183
             uu____33185
         else ());
        (let uu____33190 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____33190 with
         | (prob,x,wl) ->
             let g =
               let uu____33209 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____33220  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____33209  in
             ((let uu____33242 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____33242
               then
                 let uu____33247 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____33249 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____33251 =
                   let uu____33253 = FStar_Util.must g  in
                   guard_to_string env uu____33253  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____33247 uu____33249 uu____33251
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
        let uu____33290 = check_subtyping env t1 t2  in
        match uu____33290 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____33309 =
              let uu____33310 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____33310 g  in
            FStar_Pervasives_Native.Some uu____33309
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33329 = check_subtyping env t1 t2  in
        match uu____33329 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____33348 =
              let uu____33349 =
                let uu____33350 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____33350]  in
              FStar_TypeChecker_Env.close_guard env uu____33349 g  in
            FStar_Pervasives_Native.Some uu____33348
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____33388 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____33388
         then
           let uu____33393 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____33395 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____33393
             uu____33395
         else ());
        (let uu____33400 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____33400 with
         | (prob,x,wl) ->
             let g =
               let uu____33415 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____33426  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____33415  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____33451 =
                      let uu____33452 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____33452]  in
                    FStar_TypeChecker_Env.close_guard env uu____33451 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33493 = subtype_nosmt env t1 t2  in
        match uu____33493 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  