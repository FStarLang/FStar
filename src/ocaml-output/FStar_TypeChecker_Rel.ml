open Prims
let (print_ctx_uvar : FStar_Syntax_Syntax.ctx_uvar -> Prims.string) =
  fun ctx_uvar  -> FStar_Syntax_Print.ctx_uvar_to_string ctx_uvar 
type lstring = Prims.string FStar_Thunk.t
type uvi =
  | TERM of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | UNIV of (FStar_Syntax_Syntax.universe_uvar *
  FStar_Syntax_Syntax.universe) 
let (uu___is_TERM : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | TERM _0 -> true | uu____57 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____92 -> false
  
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
  wl_implicits: FStar_TypeChecker_Common.implicits }
let (__proj__Mkworklist__item__attempting :
  worklist -> FStar_TypeChecker_Common.probs) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> attempting
  
let (__proj__Mkworklist__item__wl_deferred :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> wl_deferred
  
let (__proj__Mkworklist__item__wl_deferred_to_tac :
  worklist ->
    (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> wl_deferred_to_tac
  
let (__proj__Mkworklist__item__ctr : worklist -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> ctr
  
let (__proj__Mkworklist__item__defer_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> defer_ok
  
let (__proj__Mkworklist__item__smt_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> smt_ok
  
let (__proj__Mkworklist__item__umax_heuristic_ok : worklist -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> umax_heuristic_ok
  
let (__proj__Mkworklist__item__tcenv : worklist -> FStar_TypeChecker_Env.env)
  =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> tcenv
  
let (__proj__Mkworklist__item__wl_implicits :
  worklist -> FStar_TypeChecker_Common.implicits) =
  fun projectee  ->
    match projectee with
    | { attempting; wl_deferred; wl_deferred_to_tac; ctr; defer_ok; smt_ok;
        umax_heuristic_ok; tcenv; wl_implicits;_} -> wl_implicits
  
let (as_deferred :
  (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list ->
    FStar_TypeChecker_Common.deferred)
  =
  fun wl_def  ->
    FStar_List.map
      (fun uu____691  ->
         match uu____691 with
         | (uu____707,m,p) ->
             let uu____718 = FStar_Thunk.force m  in (uu____718, p)) wl_def
  
let (as_wl_deferred :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun wl  ->
    fun d  ->
      FStar_List.map
        (fun uu____770  ->
           match uu____770 with
           | (m,p) ->
               let uu____790 = FStar_Thunk.mkv m  in ((wl.ctr), uu____790, p))
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
                    let uu____883 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____883;
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
                          (ctx_uvar, ([], FStar_Syntax_Syntax.NoUseRange)))
                       FStar_Pervasives_Native.None r
                      in
                   let imp =
                     {
                       FStar_TypeChecker_Common.imp_reason = reason;
                       FStar_TypeChecker_Common.imp_uvar = ctx_uvar;
                       FStar_TypeChecker_Common.imp_tm = t;
                       FStar_TypeChecker_Common.imp_range = r
                     }  in
                   (let uu____915 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____915
                    then
                      let uu____919 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____919
                    else ());
                   (ctx_uvar, t,
                     ((let uu___86_925 = wl  in
                       {
                         attempting = (uu___86_925.attempting);
                         wl_deferred = (uu___86_925.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___86_925.wl_deferred_to_tac);
                         ctr = (uu___86_925.ctr);
                         defer_ok = (uu___86_925.defer_ok);
                         smt_ok = (uu___86_925.smt_ok);
                         umax_heuristic_ok = (uu___86_925.umax_heuristic_ok);
                         tcenv = (uu___86_925.tcenv);
                         wl_implicits = (imp :: (wl.wl_implicits))
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
            let uu___92_958 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___92_958.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___92_958.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___92_958.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___92_958.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___92_958.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___92_958.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___92_958.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___92_958.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___92_958.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___92_958.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___92_958.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___92_958.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___92_958.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___92_958.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___92_958.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___92_958.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___92_958.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___92_958.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___92_958.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___92_958.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___92_958.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___92_958.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___92_958.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___92_958.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___92_958.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___92_958.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___92_958.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___92_958.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___92_958.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___92_958.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___92_958.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___92_958.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___92_958.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___92_958.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___92_958.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___92_958.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___92_958.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___92_958.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___92_958.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___92_958.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___92_958.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___92_958.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___92_958.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___92_958.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___92_958.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___92_958.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___92_958.FStar_TypeChecker_Env.enable_defer_to_tac)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____960 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____960 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____1051 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred *
      FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1092 -> false
  
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
        let uu___101_1129 = wl  in
        let uu____1130 =
          let uu____1140 = as_wl_deferred wl defer_to_tac  in
          FStar_List.append wl.wl_deferred_to_tac uu____1140  in
        {
          attempting = (uu___101_1129.attempting);
          wl_deferred = (uu___101_1129.wl_deferred);
          wl_deferred_to_tac = uu____1130;
          ctr = (uu___101_1129.ctr);
          defer_ok = (uu___101_1129.defer_ok);
          smt_ok = (uu___101_1129.smt_ok);
          umax_heuristic_ok = (uu___101_1129.umax_heuristic_ok);
          tcenv = (uu___101_1129.tcenv);
          wl_implicits = (FStar_List.append wl.wl_implicits imps)
        }
  
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____1166 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1177 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1188 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_1206  ->
    match uu___0_1206 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1218 = FStar_Syntax_Util.head_and_args t  in
    match uu____1218 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1281 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1283 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1298 =
                     let uu____1300 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1300  in
                   FStar_Util.format1 "@<%s>" uu____1298
                in
             let uu____1304 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1281 uu____1283 uu____1304
         | uu____1307 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_1319  ->
      match uu___1_1319 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1324 =
            let uu____1328 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1330 =
              let uu____1334 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1336 =
                let uu____1340 =
                  let uu____1344 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1344]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1340
                 in
              uu____1334 :: uu____1336  in
            uu____1328 :: uu____1330  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1324
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1355 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1357 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1359 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1355 uu____1357
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1359
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_1373  ->
      match uu___2_1373 with
      | UNIV (u,t) ->
          let x =
            let uu____1379 = FStar_Options.hide_uvar_nums ()  in
            if uu____1379
            then "?"
            else
              (let uu____1386 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1386 FStar_Util.string_of_int)
             in
          let uu____1390 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1390
      | TERM (u,t) ->
          let x =
            let uu____1397 = FStar_Options.hide_uvar_nums ()  in
            if uu____1397
            then "?"
            else
              (let uu____1404 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1404 FStar_Util.string_of_int)
             in
          let uu____1408 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1408
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1427 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1427 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1448 =
      let uu____1452 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1452
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1448 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1471 .
    (FStar_Syntax_Syntax.term * 'Auu____1471) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1490 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1511  ->
              match uu____1511 with
              | (x,uu____1518) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1490 (FStar_String.concat " ")
  
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
      wl_implicits = []
    }
  
let (giveup :
  FStar_TypeChecker_Env.env ->
    lstring -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        (let uu____1565 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1565
         then
           let uu____1570 = FStar_Thunk.force reason  in
           let uu____1573 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1570 uu____1573
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1596 = FStar_Thunk.mk (fun uu____1599  -> reason)  in
        giveup env uu____1596 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1605  ->
    match uu___3_1605 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1611 .
    'Auu____1611 FStar_TypeChecker_Common.problem ->
      'Auu____1611 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___161_1623 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___161_1623.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___161_1623.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___161_1623.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___161_1623.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___161_1623.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___161_1623.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___161_1623.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1631 .
    'Auu____1631 FStar_TypeChecker_Common.problem ->
      'Auu____1631 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1651  ->
    match uu___4_1651 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1657  -> FStar_TypeChecker_Common.TProb _1657)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1663  -> FStar_TypeChecker_Common.CProb _1663)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1669  ->
    match uu___5_1669 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___173_1675 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___173_1675.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___173_1675.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___173_1675.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___173_1675.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___173_1675.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___173_1675.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___173_1675.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___173_1675.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___173_1675.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___177_1683 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___177_1683.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___177_1683.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___177_1683.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___177_1683.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___177_1683.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___177_1683.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___177_1683.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___177_1683.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___177_1683.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1696  ->
      match uu___6_1696 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1703  ->
    match uu___7_1703 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1716  ->
    match uu___8_1716 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1731  ->
    match uu___9_1731 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1746  ->
    match uu___10_1746 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1760  ->
    match uu___11_1760 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1774  ->
    match uu___12_1774 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1786  ->
    match uu___13_1786 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1802 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1802) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1832 =
          let uu____1834 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1834  in
        if uu____1832
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1871)::bs ->
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
          let uu____1918 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1942 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1942]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1918
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1970 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1994 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1994]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1970
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____2041 =
          let uu____2043 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2043  in
        if uu____2041
        then ()
        else
          (let uu____2048 =
             let uu____2051 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____2051
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____2048 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____2100 =
          let uu____2102 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2102  in
        if uu____2100
        then ()
        else
          (let uu____2107 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____2107)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____2127 =
        let uu____2129 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____2129  in
      if uu____2127
      then ()
      else
        (let msgf m =
           let uu____2143 =
             let uu____2145 =
               let uu____2147 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____2147 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____2145  in
           Prims.op_Hat msg uu____2143  in
         (let uu____2152 = msgf "scope"  in
          let uu____2155 = p_scope prob  in
          def_scope_wf uu____2152 (p_loc prob) uu____2155);
         (let uu____2167 = msgf "guard"  in
          def_check_scoped uu____2167 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____2174 = msgf "lhs"  in
                def_check_scoped uu____2174 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2177 = msgf "rhs"  in
                def_check_scoped uu____2177 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____2184 = msgf "lhs"  in
                def_check_scoped_comp uu____2184 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2187 = msgf "rhs"  in
                def_check_scoped_comp uu____2187 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___270_2208 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___270_2208.wl_deferred);
          wl_deferred_to_tac = (uu___270_2208.wl_deferred_to_tac);
          ctr = (uu___270_2208.ctr);
          defer_ok = (uu___270_2208.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___270_2208.umax_heuristic_ok);
          tcenv = (uu___270_2208.tcenv);
          wl_implicits = (uu___270_2208.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____2216 .
    FStar_TypeChecker_Env.env ->
      ('Auu____2216 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___274_2239 = empty_worklist env  in
      let uu____2240 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____2240;
        wl_deferred = (uu___274_2239.wl_deferred);
        wl_deferred_to_tac = (uu___274_2239.wl_deferred_to_tac);
        ctr = (uu___274_2239.ctr);
        defer_ok = (uu___274_2239.defer_ok);
        smt_ok = (uu___274_2239.smt_ok);
        umax_heuristic_ok = (uu___274_2239.umax_heuristic_ok);
        tcenv = (uu___274_2239.tcenv);
        wl_implicits = (uu___274_2239.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___279_2261 = wl  in
        {
          attempting = (uu___279_2261.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          wl_deferred_to_tac = (uu___279_2261.wl_deferred_to_tac);
          ctr = (uu___279_2261.ctr);
          defer_ok = (uu___279_2261.defer_ok);
          smt_ok = (uu___279_2261.smt_ok);
          umax_heuristic_ok = (uu___279_2261.umax_heuristic_ok);
          tcenv = (uu___279_2261.tcenv);
          wl_implicits = (uu___279_2261.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____2288 = FStar_Thunk.mkv reason  in defer uu____2288 prob wl
  
let (should_defer_uvar_to_user_tac :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun env  ->
    fun u  ->
      if Prims.op_Negation env.FStar_TypeChecker_Env.enable_defer_to_tac
      then false
      else
        (match u.FStar_Syntax_Syntax.ctx_uvar_meta with
         | FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Ctx_uvar_meta_attr a) ->
             let hooks =
               FStar_TypeChecker_Env.lookup_attr env
                 FStar_Parser_Const.resolve_implicits_attr_string
                in
             let should_defer =
               FStar_All.pipe_right hooks
                 (FStar_Util.for_some
                    (fun hook  ->
                       FStar_All.pipe_right hook.FStar_Syntax_Syntax.sigattrs
                         (FStar_Util.for_some (FStar_Syntax_Util.attr_eq a))))
                in
             should_defer
         | uu____2324 -> false)
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___297_2345 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___297_2345.wl_deferred);
         wl_deferred_to_tac = (uu___297_2345.wl_deferred_to_tac);
         ctr = (uu___297_2345.ctr);
         defer_ok = (uu___297_2345.defer_ok);
         smt_ok = (uu___297_2345.smt_ok);
         umax_heuristic_ok = (uu___297_2345.umax_heuristic_ok);
         tcenv = (uu___297_2345.tcenv);
         wl_implicits = (uu___297_2345.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____2359 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2359 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____2393 = FStar_Syntax_Util.type_u ()  in
            match uu____2393 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____2405 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____2405 with
                 | (uu____2417,tt,wl1) ->
                     let uu____2420 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2420, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2426  ->
    match uu___14_2426 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _2432  -> FStar_TypeChecker_Common.TProb _2432) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _2438  -> FStar_TypeChecker_Common.CProb _2438) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2446 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2446 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2466  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2508 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2508 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2508 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2508 FStar_TypeChecker_Common.problem *
                      worklist)
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
                        let uu____2595 =
                          let uu____2604 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2604]  in
                        FStar_List.append scope uu____2595
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2647 =
                      let uu____2650 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2650  in
                    FStar_List.append uu____2647
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2669 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2669 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2689 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2689;
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
                  (let uu____2763 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2763 with
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
                  (let uu____2851 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2851 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2889 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2889 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2889 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2889 FStar_TypeChecker_Common.problem *
                      worklist)
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
                          let uu____2957 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2957]  in
                        let uu____2976 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2976
                     in
                  let uu____2979 =
                    let uu____2986 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___380_2997 = wl  in
                       {
                         attempting = (uu___380_2997.attempting);
                         wl_deferred = (uu___380_2997.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___380_2997.wl_deferred_to_tac);
                         ctr = (uu___380_2997.ctr);
                         defer_ok = (uu___380_2997.defer_ok);
                         smt_ok = (uu___380_2997.smt_ok);
                         umax_heuristic_ok =
                           (uu___380_2997.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___380_2997.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2986
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2979 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____3009 =
                              let uu____3014 =
                                let uu____3015 =
                                  let uu____3024 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____3024
                                   in
                                [uu____3015]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____3014  in
                            uu____3009 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____3052 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____3052;
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
                let uu____3100 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____3100;
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
  'Auu____3115 .
    worklist ->
      'Auu____3115 FStar_TypeChecker_Common.problem ->
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
              let uu____3148 =
                let uu____3151 =
                  let uu____3152 =
                    let uu____3159 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____3159)  in
                  FStar_Syntax_Syntax.NT uu____3152  in
                [uu____3151]  in
              FStar_Syntax_Subst.subst uu____3148 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____3181 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____3181
        then
          let uu____3189 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____3192 = prob_to_string env d  in
          let uu____3194 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____3201 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3189 uu____3192 uu____3194 uu____3201
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____3213 -> failwith "impossible"  in
           let uu____3216 =
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
           match uu____3216 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3259  ->
            match uu___15_3259 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3271 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____3275 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3275 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_3306  ->
           match uu___16_3306 with
           | UNIV uu____3309 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____3316 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____3316
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
        (fun uu___17_3344  ->
           match uu___17_3344 with
           | UNIV (u',t) ->
               let uu____3349 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____3349
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3356 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3368 =
        let uu____3369 =
          let uu____3370 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3370
           in
        FStar_Syntax_Subst.compress uu____3369  in
      FStar_All.pipe_right uu____3368 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3382 =
        let uu____3383 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3383  in
      FStar_All.pipe_right uu____3382 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3395 =
        let uu____3399 =
          let uu____3401 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3401  in
        FStar_Pervasives_Native.Some uu____3399  in
      FStar_Profiling.profile (fun uu____3404  -> sn' env t) uu____3395
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
          let uu____3429 =
            let uu____3433 =
              let uu____3435 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3435  in
            FStar_Pervasives_Native.Some uu____3433  in
          FStar_Profiling.profile
            (fun uu____3438  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3429
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3446 = FStar_Syntax_Util.head_and_args t  in
    match uu____3446 with
    | (h,uu____3465) ->
        let uu____3490 =
          let uu____3491 = FStar_Syntax_Subst.compress h  in
          uu____3491.FStar_Syntax_Syntax.n  in
        (match uu____3490 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3496 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3509 =
        let uu____3513 =
          let uu____3515 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3515  in
        FStar_Pervasives_Native.Some uu____3513  in
      FStar_Profiling.profile
        (fun uu____3520  ->
           let uu____3521 = should_strongly_reduce t  in
           if uu____3521
           then
             let uu____3524 =
               let uu____3525 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3525  in
             FStar_All.pipe_right uu____3524 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3509 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3536 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3536) ->
        (FStar_Syntax_Syntax.term * 'Auu____3536)
  =
  fun env  ->
    fun t  ->
      let uu____3559 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3559, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3611  ->
              match uu____3611 with
              | (x,imp) ->
                  let uu____3630 =
                    let uu___486_3631 = x  in
                    let uu____3632 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___486_3631.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___486_3631.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3632
                    }  in
                  (uu____3630, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3656 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3656
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3660 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3660
        | uu____3663 -> u2  in
      let uu____3664 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3664
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3681 =
          let uu____3685 =
            let uu____3687 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3687  in
          FStar_Pervasives_Native.Some uu____3685  in
        FStar_Profiling.profile
          (fun uu____3690  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3681 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
        let rec aux norm1 t11 =
          let t12 = FStar_Syntax_Util.unmeta t11  in
          match t12.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
              if norm1
              then
                ((x.FStar_Syntax_Syntax.sort),
                  (FStar_Pervasives_Native.Some (x, phi)))
              else
                (let uu____3812 = norm_refinement env t12  in
                 match uu____3812 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3827;
                     FStar_Syntax_Syntax.vars = uu____3828;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3852 =
                       let uu____3854 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3856 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3854 uu____3856
                        in
                     failwith uu____3852)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3872 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3872
          | FStar_Syntax_Syntax.Tm_uinst uu____3873 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3910 =
                   let uu____3911 = FStar_Syntax_Subst.compress t1'  in
                   uu____3911.FStar_Syntax_Syntax.n  in
                 match uu____3910 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3926 -> aux true t1'
                 | uu____3934 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3949 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3980 =
                   let uu____3981 = FStar_Syntax_Subst.compress t1'  in
                   uu____3981.FStar_Syntax_Syntax.n  in
                 match uu____3980 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3996 -> aux true t1'
                 | uu____4004 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4019 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4066 =
                   let uu____4067 = FStar_Syntax_Subst.compress t1'  in
                   uu____4067.FStar_Syntax_Syntax.n  in
                 match uu____4066 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4082 -> aux true t1'
                 | uu____4090 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____4105 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____4120 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____4135 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____4150 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____4165 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____4194 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____4227 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____4248 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____4275 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____4303 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____4340 ->
              let uu____4347 =
                let uu____4349 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4351 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4349 uu____4351
                 in
              failwith uu____4347
          | FStar_Syntax_Syntax.Tm_ascribed uu____4366 ->
              let uu____4393 =
                let uu____4395 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4397 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4395 uu____4397
                 in
              failwith uu____4393
          | FStar_Syntax_Syntax.Tm_delayed uu____4412 ->
              let uu____4427 =
                let uu____4429 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4431 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4429 uu____4431
                 in
              failwith uu____4427
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4446 =
                let uu____4448 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4450 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4448 uu____4450
                 in
              failwith uu____4446
           in
        let uu____4465 = whnf env t1  in aux false uu____4465
  
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
      let uu____4510 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4510 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4551 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4551, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4578 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4578 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4638  ->
    match uu____4638 with
    | (t_base,refopt) ->
        let uu____4669 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4669 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4711 =
      let uu____4715 =
        let uu____4718 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4743  ->
                  match uu____4743 with | (uu____4751,uu____4752,x) -> x))
           in
        FStar_List.append wl.attempting uu____4718  in
      FStar_List.map (wl_prob_to_string wl) uu____4715  in
    FStar_All.pipe_right uu____4711 (FStar_String.concat "\n\t")
  
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
  fun uu____4812  ->
    match uu____4812 with
    | Flex (uu____4814,u,uu____4816) -> u.FStar_Syntax_Syntax.ctx_uvar_reason
  
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4823  ->
    match uu____4823 with
    | Flex (uu____4825,c,args) ->
        let uu____4828 = print_ctx_uvar c  in
        let uu____4830 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4828 uu____4830
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4840 = FStar_Syntax_Util.head_and_args t  in
    match uu____4840 with
    | (head1,_args) ->
        let uu____4884 =
          let uu____4885 = FStar_Syntax_Subst.compress head1  in
          uu____4885.FStar_Syntax_Syntax.n  in
        (match uu____4884 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4889 -> true
         | uu____4903 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4911 = FStar_Syntax_Util.head_and_args t  in
    match uu____4911 with
    | (head1,_args) ->
        let uu____4954 =
          let uu____4955 = FStar_Syntax_Subst.compress head1  in
          uu____4955.FStar_Syntax_Syntax.n  in
        (match uu____4954 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4959) -> u
         | uu____4976 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____5001 = FStar_Syntax_Util.head_and_args t  in
      match uu____5001 with
      | (head1,args) ->
          let uu____5048 =
            let uu____5049 = FStar_Syntax_Subst.compress head1  in
            uu____5049.FStar_Syntax_Syntax.n  in
          (match uu____5048 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____5057)) ->
               ((Flex (t, uv, args)), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____5090 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_5115  ->
                         match uu___18_5115 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____5120 =
                               let uu____5121 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____5121.FStar_Syntax_Syntax.n  in
                             (match uu____5120 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____5126 -> false)
                         | uu____5128 -> true))
                  in
               (match uu____5090 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____5153 =
                        FStar_List.collect
                          (fun uu___19_5165  ->
                             match uu___19_5165 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____5169 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____5169]
                             | uu____5170 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____5153 FStar_List.rev  in
                    let uu____5193 =
                      let uu____5200 =
                        let uu____5209 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_5231  ->
                                  match uu___20_5231 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____5235 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____5235]
                                  | uu____5236 -> []))
                           in
                        FStar_All.pipe_right uu____5209 FStar_List.rev  in
                      let uu____5259 =
                        let uu____5262 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____5262  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____5200 uu____5259
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____5193 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____5298  ->
                                match uu____5298 with
                                | (x,i) ->
                                    let uu____5317 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____5317, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____5348  ->
                                match uu____5348 with
                                | (a,i) ->
                                    let uu____5367 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____5367, i)) args_sol
                            in
                         let all_args = FStar_List.append args_sol_s args  in
                         let t1 =
                           FStar_Syntax_Syntax.mk_Tm_app t_v all_args
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         (FStar_Syntax_Unionfind.change
                            uv.FStar_Syntax_Syntax.ctx_uvar_head sol;
                          ((Flex (t1, v1, all_args)), wl1))))
           | uu____5389 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5411 =
          let uu____5434 =
            let uu____5435 = FStar_Syntax_Subst.compress k  in
            uu____5435.FStar_Syntax_Syntax.n  in
          match uu____5434 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5517 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5517)
              else
                (let uu____5552 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5552 with
                 | (ys',t1,uu____5585) ->
                     let uu____5590 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5590))
          | uu____5629 ->
              let uu____5630 =
                let uu____5635 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5635)  in
              ((ys, t), uu____5630)
           in
        match uu____5411 with
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
                 let uu____5730 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5730 c  in
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
               (let uu____5808 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5808
                then
                  let uu____5813 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5815 = print_ctx_uvar uv  in
                  let uu____5817 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5813 uu____5815 uu____5817
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5826 =
                   let uu____5828 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5828  in
                 let uu____5831 =
                   let uu____5834 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5834
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5826 uu____5831 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5867 =
               let uu____5868 =
                 let uu____5870 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5872 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5870 uu____5872
                  in
               failwith uu____5868  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5938  ->
                       match uu____5938 with
                       | (a,i) ->
                           let uu____5959 =
                             let uu____5960 = FStar_Syntax_Subst.compress a
                                in
                             uu____5960.FStar_Syntax_Syntax.n  in
                           (match uu____5959 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5986 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5996 =
                 let uu____5998 = is_flex g  in Prims.op_Negation uu____5998
                  in
               if uu____5996
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____6007 = destruct_flex_t g wl  in
                  match uu____6007 with
                  | (Flex (uu____6012,uv1,args),wl1) ->
                      ((let uu____6017 = args_as_binders args  in
                        assign_solution uu____6017 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___748_6019 = wl1  in
              {
                attempting = (uu___748_6019.attempting);
                wl_deferred = (uu___748_6019.wl_deferred);
                wl_deferred_to_tac = (uu___748_6019.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___748_6019.defer_ok);
                smt_ok = (uu___748_6019.smt_ok);
                umax_heuristic_ok = (uu___748_6019.umax_heuristic_ok);
                tcenv = (uu___748_6019.tcenv);
                wl_implicits = (uu___748_6019.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____6044 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____6044
         then
           let uu____6049 = FStar_Util.string_of_int pid  in
           let uu____6051 =
             let uu____6053 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____6053 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6049 uu____6051
         else ());
        commit sol;
        (let uu___756_6067 = wl  in
         {
           attempting = (uu___756_6067.attempting);
           wl_deferred = (uu___756_6067.wl_deferred);
           wl_deferred_to_tac = (uu___756_6067.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___756_6067.defer_ok);
           smt_ok = (uu___756_6067.smt_ok);
           umax_heuristic_ok = (uu___756_6067.umax_heuristic_ok);
           tcenv = (uu___756_6067.tcenv);
           wl_implicits = (uu___756_6067.wl_implicits)
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
          (let uu____6103 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____6103
           then
             let uu____6108 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____6112 =
               let uu____6114 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____6114 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6108 uu____6112
           else ());
          solve_prob' false prob logical_guard uvis wl
  
let (occurs :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool))
  =
  fun uk  ->
    fun t  ->
      let uvars1 =
        let uu____6149 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____6149 FStar_Util.set_elements  in
      let occurs =
        FStar_All.pipe_right uvars1
          (FStar_Util.for_some
             (fun uv  ->
                FStar_Syntax_Unionfind.equiv
                  uv.FStar_Syntax_Syntax.ctx_uvar_head
                  uk.FStar_Syntax_Syntax.ctx_uvar_head))
         in
      (uvars1, occurs)
  
let (occurs_check :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.ctx_uvar Prims.list * Prims.bool * Prims.string
        FStar_Pervasives_Native.option))
  =
  fun uk  ->
    fun t  ->
      let uu____6189 = occurs uk t  in
      match uu____6189 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6228 =
                 let uu____6230 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____6232 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6230 uu____6232
                  in
               FStar_Pervasives_Native.Some uu____6228)
             in
          (uvars1, (Prims.op_Negation occurs1), msg)
  
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
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            let uu____6352 = maximal_prefix bs_tail bs'_tail  in
            (match uu____6352 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6403 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6460  ->
             match uu____6460 with
             | (x,uu____6472) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6490 = FStar_List.last bs  in
      match uu____6490 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6514) ->
          let uu____6525 =
            FStar_Util.prefix_until
              (fun uu___21_6540  ->
                 match uu___21_6540 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6543 -> false) g
             in
          (match uu____6525 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6557,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6594 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6594 with
        | (pfx,uu____6604) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6616 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6616 with
             | (uu____6624,src',wl1) ->
                 (FStar_Syntax_Unionfind.change
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
        let as_set1 v3 =
          FStar_All.pipe_right v3
            (FStar_List.fold_left
               (fun out  ->
                  fun x  ->
                    FStar_Util.set_add (FStar_Pervasives_Native.fst x) out)
               FStar_Syntax_Syntax.no_names)
           in
        let v1_set = as_set1 v1  in
        let ctx_binders =
          FStar_List.fold_left
            (fun out  ->
               fun b  ->
                 match b with
                 | FStar_Syntax_Syntax.Binding_var x ->
                     FStar_Util.set_add x out
                 | uu____6738 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6739 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6803  ->
                  fun uu____6804  ->
                    match (uu____6803, uu____6804) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6907 =
                          let uu____6909 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6909
                           in
                        if uu____6907
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6943 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6943
                           then
                             let uu____6960 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6960)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6739 with | (isect,uu____7010) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____7046 'Auu____7047 .
    (FStar_Syntax_Syntax.bv * 'Auu____7046) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____7047) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7105  ->
              fun uu____7106  ->
                match (uu____7105, uu____7106) with
                | ((a,uu____7125),(b,uu____7127)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____7143 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____7143) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____7174  ->
           match uu____7174 with
           | (y,uu____7181) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____7191 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____7191) Prims.list ->
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
              let hd1 = sn env arg  in
              (match hd1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_name a ->
                   let uu____7353 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____7353
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7386 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7438 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7482 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7503 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7511  ->
    match uu___22_7511 with
    | MisMatch (d1,d2) ->
        let uu____7523 =
          let uu____7525 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7527 =
            let uu____7529 =
              let uu____7531 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7531 ")"  in
            Prims.op_Hat ") (" uu____7529  in
          Prims.op_Hat uu____7525 uu____7527  in
        Prims.op_Hat "MisMatch (" uu____7523
    | HeadMatch u ->
        let uu____7538 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7538
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7547  ->
    match uu___23_7547 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7564 -> HeadMatch false
  
let (fv_delta_depth :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.delta_depth)
  =
  fun env  ->
    fun fv  ->
      let d = FStar_TypeChecker_Env.delta_depth_of_fv env fv  in
      match d with
      | FStar_Syntax_Syntax.Delta_abstract d1 ->
          if
            ((env.FStar_TypeChecker_Env.curmodule).FStar_Ident.str =
               ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.nsstr)
              && (Prims.op_Negation env.FStar_TypeChecker_Env.is_iface)
          then d1
          else FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Delta_constant_at_level i when i > Prims.int_zero
          ->
          let uu____7586 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7586 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7597 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7621 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7631 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7650 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7650
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7651 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7652 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7653 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7666 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7680 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7704) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7710,uu____7711) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7753) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7778;
             FStar_Syntax_Syntax.index = uu____7779;
             FStar_Syntax_Syntax.sort = t2;_},uu____7781)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7789 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7790 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7791 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7806 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7813 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7833 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7833
  
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
           { FStar_Syntax_Syntax.blob = uu____7852;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7853;
             FStar_Syntax_Syntax.ltyp = uu____7854;
             FStar_Syntax_Syntax.rng = uu____7855;_},uu____7856)
            ->
            let uu____7867 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7867 t21
        | (uu____7868,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7869;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7870;
             FStar_Syntax_Syntax.ltyp = uu____7871;
             FStar_Syntax_Syntax.rng = uu____7872;_})
            ->
            let uu____7883 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7883
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7895 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7895
            then FullMatch
            else
              (let uu____7900 =
                 let uu____7909 =
                   let uu____7912 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7912  in
                 let uu____7913 =
                   let uu____7916 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7916  in
                 (uu____7909, uu____7913)  in
               MisMatch uu____7900)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7922),FStar_Syntax_Syntax.Tm_uinst (g,uu____7924)) ->
            let uu____7933 = head_matches env f g  in
            FStar_All.pipe_right uu____7933 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7934) -> HeadMatch true
        | (uu____7936,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7940 = FStar_Const.eq_const c d  in
            if uu____7940
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7950),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7952)) ->
            let uu____7985 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7985
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7995),FStar_Syntax_Syntax.Tm_refine (y,uu____7997)) ->
            let uu____8006 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8006 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____8008),uu____8009) ->
            let uu____8014 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____8014 head_match
        | (uu____8015,FStar_Syntax_Syntax.Tm_refine (x,uu____8017)) ->
            let uu____8022 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8022 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8023,FStar_Syntax_Syntax.Tm_type
           uu____8024) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____8026,FStar_Syntax_Syntax.Tm_arrow uu____8027) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____8058),FStar_Syntax_Syntax.Tm_app (head',uu____8060))
            ->
            let uu____8109 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____8109 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____8111),uu____8112) ->
            let uu____8137 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____8137 head_match
        | (uu____8138,FStar_Syntax_Syntax.Tm_app (head1,uu____8140)) ->
            let uu____8165 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____8165 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8166,FStar_Syntax_Syntax.Tm_let
           uu____8167) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____8195,FStar_Syntax_Syntax.Tm_match uu____8196) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8242,FStar_Syntax_Syntax.Tm_abs
           uu____8243) -> HeadMatch true
        | uu____8281 ->
            let uu____8286 =
              let uu____8295 = delta_depth_of_term env t11  in
              let uu____8298 = delta_depth_of_term env t21  in
              (uu____8295, uu____8298)  in
            MisMatch uu____8286
  
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
            let head1 =
              let uu____8367 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8367  in
            (let uu____8369 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8369
             then
               let uu____8374 = FStar_Syntax_Print.term_to_string t  in
               let uu____8376 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8374 uu____8376
             else ());
            (let uu____8381 =
               let uu____8382 = FStar_Syntax_Util.un_uinst head1  in
               uu____8382.FStar_Syntax_Syntax.n  in
             match uu____8381 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8388 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8388 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8402 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8402
                        then
                          let uu____8407 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8407
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8412 ->
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
                      let uu____8430 =
                        let uu____8432 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8432 = FStar_Syntax_Util.Equal  in
                      if uu____8430
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8439 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8439
                          then
                            let uu____8444 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8446 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8444
                              uu____8446
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8451 -> FStar_Pervasives_Native.None)
             in
          let success d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let fail1 d r t11 t21 =
            (r,
              (if d > Prims.int_zero
               then FStar_Pervasives_Native.Some (t11, t21)
               else FStar_Pervasives_Native.None))
             in
          let rec aux retry1 n_delta t11 t21 =
            let r = head_matches env t11 t21  in
            (let uu____8603 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8603
             then
               let uu____8608 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8610 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8612 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8608
                 uu____8610 uu____8612
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8640 =
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
               match uu____8640 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8688 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8688 with
               | FStar_Pervasives_Native.None  -> fail1 n_delta r1 t11 t21
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
                   aux retry1 (n_delta + Prims.int_one) t12 t22
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
                  uu____8726),uu____8727)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8748 =
                      let uu____8757 = maybe_inline t11  in
                      let uu____8760 = maybe_inline t21  in
                      (uu____8757, uu____8760)  in
                    match uu____8748 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
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
                 (uu____8803,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8804))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8825 =
                      let uu____8834 = maybe_inline t11  in
                      let uu____8837 = maybe_inline t21  in
                      (uu____8834, uu____8837)  in
                    match uu____8825 with
                    | (FStar_Pervasives_Native.None
                       ,FStar_Pervasives_Native.None ) ->
                        fail1 n_delta r t11 t21
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
             | MisMatch uu____8892 -> fail1 n_delta r t11 t21
             | uu____8901 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8916 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8916
           then
             let uu____8921 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8923 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8925 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8933 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8950 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8950
                    (fun uu____8985  ->
                       match uu____8985 with
                       | (t11,t21) ->
                           let uu____8993 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8995 =
                             let uu____8997 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8997  in
                           Prims.op_Hat uu____8993 uu____8995))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8921 uu____8923 uu____8925 uu____8933
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____9014 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____9014 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_9029  ->
    match uu___24_9029 with
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
      let uu___1245_9078 = p  in
      let uu____9081 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____9082 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1245_9078.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9081;
        FStar_TypeChecker_Common.relation =
          (uu___1245_9078.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9082;
        FStar_TypeChecker_Common.element =
          (uu___1245_9078.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1245_9078.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1245_9078.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1245_9078.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1245_9078.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1245_9078.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9097 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____9097
            (fun _9102  -> FStar_TypeChecker_Common.TProb _9102)
      | FStar_TypeChecker_Common.CProb uu____9103 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____9126 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____9126 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9134 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9134 with
           | (lh,lhs_args) ->
               let uu____9181 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9181 with
                | (rh,rhs_args) ->
                    let uu____9228 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9241,FStar_Syntax_Syntax.Tm_uvar uu____9242)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9331 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9358,uu____9359)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9374,FStar_Syntax_Syntax.Tm_uvar uu____9375)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9390,FStar_Syntax_Syntax.Tm_arrow uu____9391)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1296_9421 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1296_9421.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1296_9421.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1296_9421.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1296_9421.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1296_9421.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1296_9421.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1296_9421.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1296_9421.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1296_9421.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9424,FStar_Syntax_Syntax.Tm_type uu____9425)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1296_9441 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1296_9441.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1296_9441.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1296_9441.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1296_9441.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1296_9441.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1296_9441.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1296_9441.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1296_9441.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1296_9441.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9444,FStar_Syntax_Syntax.Tm_uvar uu____9445)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1296_9461 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1296_9461.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1296_9461.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1296_9461.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1296_9461.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1296_9461.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1296_9461.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1296_9461.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1296_9461.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1296_9461.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9464,FStar_Syntax_Syntax.Tm_uvar uu____9465)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9480,uu____9481)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9496,FStar_Syntax_Syntax.Tm_uvar uu____9497)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9512,uu____9513) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9228 with
                     | (rank,tp1) ->
                         let uu____9526 =
                           FStar_All.pipe_right
                             (let uu___1316_9530 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1316_9530.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1316_9530.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1316_9530.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1316_9530.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1316_9530.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1316_9530.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1316_9530.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1316_9530.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1316_9530.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9533  ->
                                FStar_TypeChecker_Common.TProb _9533)
                            in
                         (rank, uu____9526))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9537 =
            FStar_All.pipe_right
              (let uu___1320_9541 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1320_9541.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1320_9541.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1320_9541.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1320_9541.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1320_9541.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1320_9541.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1320_9541.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1320_9541.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1320_9541.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9544  -> FStar_TypeChecker_Common.CProb _9544)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9537)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9604 probs =
      match uu____9604 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9685 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9706 = rank wl.tcenv hd1  in
               (match uu____9706 with
                | (rank1,hd2) ->
                    if rank_leq rank1 FStar_TypeChecker_Common.Flex_rigid_eq
                    then
                      (match min1 with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out tl1), rank1)
                       | FStar_Pervasives_Native.Some m ->
                           FStar_Pervasives_Native.Some
                             (hd2, (FStar_List.append out (m :: tl1)), rank1))
                    else
                      (let uu____9767 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9772 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9772)
                          in
                       if uu____9767
                       then
                         match min1 with
                         | FStar_Pervasives_Native.None  ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), out) tl1
                         | FStar_Pervasives_Native.Some m ->
                             aux
                               ((FStar_Pervasives_Native.Some rank1),
                                 (FStar_Pervasives_Native.Some hd2), (m ::
                                 out)) tl1
                       else aux (min_rank, min1, (hd2 :: out)) tl1)))
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
          let uu____9845 = FStar_Syntax_Util.head_and_args t  in
          match uu____9845 with
          | (hd1,uu____9864) ->
              let uu____9889 =
                let uu____9890 = FStar_Syntax_Subst.compress hd1  in
                uu____9890.FStar_Syntax_Syntax.n  in
              (match uu____9889 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9895) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9930  ->
                           match uu____9930 with
                           | (y,uu____9939) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9962  ->
                                       match uu____9962 with
                                       | (x,uu____9971) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9976 -> false)
           in
        let uu____9978 = rank tcenv p  in
        match uu____9978 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9987 -> true
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
    match projectee with | UDeferred _0 -> true | uu____10068 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____10087 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____10106 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____10123 = FStar_Thunk.mkv s  in UFailed uu____10123 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____10138 = FStar_Thunk.mk s  in UFailed uu____10138 
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
                        let uu____10190 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____10190 with
                        | (k,uu____10198) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10211 -> false)))
            | uu____10213 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10265 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____10273 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____10273 = Prims.int_zero))
                           in
                        if uu____10265 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____10294 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____10302 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____10302 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____10294)
               in
            let uu____10306 = filter1 u12  in
            let uu____10309 = filter1 u22  in (uu____10306, uu____10309)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10344 = filter_out_common_univs us1 us2  in
                   (match uu____10344 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10404 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10404 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10407 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10424  ->
                               let uu____10425 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10427 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10425 uu____10427))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10453 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10453 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10479 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10479 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10482 ->
                   ufailed_thunk
                     (fun uu____10493  ->
                        let uu____10494 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10496 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10494 uu____10496 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10499,uu____10500) ->
              let uu____10502 =
                let uu____10504 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10506 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10504 uu____10506
                 in
              failwith uu____10502
          | (FStar_Syntax_Syntax.U_unknown ,uu____10509) ->
              let uu____10510 =
                let uu____10512 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10514 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10512 uu____10514
                 in
              failwith uu____10510
          | (uu____10517,FStar_Syntax_Syntax.U_bvar uu____10518) ->
              let uu____10520 =
                let uu____10522 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10524 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10522 uu____10524
                 in
              failwith uu____10520
          | (uu____10527,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10528 =
                let uu____10530 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10532 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10530 uu____10532
                 in
              failwith uu____10528
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10562 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10562
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10579 = occurs_univ v1 u3  in
              if uu____10579
              then
                let uu____10582 =
                  let uu____10584 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10586 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10584 uu____10586
                   in
                try_umax_components u11 u21 uu____10582
              else
                (let uu____10591 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10591)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10603 = occurs_univ v1 u3  in
              if uu____10603
              then
                let uu____10606 =
                  let uu____10608 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10610 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10608 uu____10610
                   in
                try_umax_components u11 u21 uu____10606
              else
                (let uu____10615 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10615)
          | (FStar_Syntax_Syntax.U_max uu____10616,uu____10617) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10625 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10625
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10631,FStar_Syntax_Syntax.U_max uu____10632) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10640 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10640
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10646,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10648,FStar_Syntax_Syntax.U_name uu____10649) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10651) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10653) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10655,FStar_Syntax_Syntax.U_succ uu____10656) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10658,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10765 = bc1  in
      match uu____10765 with
      | (bs1,mk_cod1) ->
          let uu____10809 = bc2  in
          (match uu____10809 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10920 = aux xs ys  in
                     (match uu____10920 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____11003 =
                       let uu____11010 = mk_cod1 xs  in ([], uu____11010)  in
                     let uu____11013 =
                       let uu____11020 = mk_cod2 ys  in ([], uu____11020)  in
                     (uu____11003, uu____11013)
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
                  let uu____11089 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____11089 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____11092 =
                    let uu____11093 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____11093 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____11092
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____11098 = has_type_guard t1 t2  in (uu____11098, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____11099 = has_type_guard t2 t1  in (uu____11099, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___25_11106  ->
    match uu___25_11106 with
    | Flex (uu____11108,uu____11109,[]) -> true
    | uu____11119 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____11133 = f  in
      match uu____11133 with
      | Flex (uu____11135,u,uu____11137) ->
          should_defer_uvar_to_user_tac wl.tcenv u
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____11161 = f  in
      match uu____11161 with
      | Flex
          (uu____11168,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____11169;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11170;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____11173;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____11174;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____11175;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____11176;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11240  ->
                 match uu____11240 with
                 | (y,uu____11249) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11403 =
                  let uu____11418 =
                    let uu____11421 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11421  in
                  ((FStar_List.rev pat_binders), uu____11418)  in
                FStar_Pervasives_Native.Some uu____11403
            | (uu____11454,[]) ->
                let uu____11485 =
                  let uu____11500 =
                    let uu____11503 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11503  in
                  ((FStar_List.rev pat_binders), uu____11500)  in
                FStar_Pervasives_Native.Some uu____11485
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11594 =
                  let uu____11595 = FStar_Syntax_Subst.compress a  in
                  uu____11595.FStar_Syntax_Syntax.n  in
                (match uu____11594 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11615 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11615
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1657_11645 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1657_11645.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1657_11645.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11649 =
                            let uu____11650 =
                              let uu____11657 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11657)  in
                            FStar_Syntax_Syntax.NT uu____11650  in
                          [uu____11649]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1663_11673 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1663_11673.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1663_11673.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11674 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11714 =
                  let uu____11721 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11721  in
                (match uu____11714 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11780 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11805 ->
               let uu____11806 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11806 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____12138 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____12138
       then
         let uu____12143 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12143
       else ());
      (let uu____12149 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____12149
       then
         let uu____12154 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12154
       else ());
      (let uu____12159 = next_prob probs  in
       match uu____12159 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1690_12186 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1690_12186.wl_deferred);
               wl_deferred_to_tac = (uu___1690_12186.wl_deferred_to_tac);
               ctr = (uu___1690_12186.ctr);
               defer_ok = (uu___1690_12186.defer_ok);
               smt_ok = (uu___1690_12186.smt_ok);
               umax_heuristic_ok = (uu___1690_12186.umax_heuristic_ok);
               tcenv = (uu___1690_12186.tcenv);
               wl_implicits = (uu___1690_12186.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12195 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____12195
                 then
                   let uu____12198 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____12198
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
                           (let uu___1702_12210 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1702_12210.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1702_12210.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1702_12210.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1702_12210.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1702_12210.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1702_12210.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1702_12210.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1702_12210.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1702_12210.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12230 =
                  let uu____12237 = as_deferred probs.wl_deferred_to_tac  in
                  ([], uu____12237, (probs.wl_implicits))  in
                Success uu____12230
            | uu____12243 ->
                let uu____12253 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12318  ->
                          match uu____12318 with
                          | (c,uu____12328,uu____12329) -> c < probs.ctr))
                   in
                (match uu____12253 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12377 =
                            let uu____12384 = as_deferred probs.wl_deferred
                               in
                            let uu____12385 =
                              as_deferred probs.wl_deferred_to_tac  in
                            (uu____12384, uu____12385, (probs.wl_implicits))
                             in
                          Success uu____12377
                      | uu____12386 ->
                          let uu____12396 =
                            let uu___1716_12397 = probs  in
                            let uu____12398 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12419  ->
                                      match uu____12419 with
                                      | (uu____12427,uu____12428,y) -> y))
                               in
                            {
                              attempting = uu____12398;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1716_12397.wl_deferred_to_tac);
                              ctr = (uu___1716_12397.ctr);
                              defer_ok = (uu___1716_12397.defer_ok);
                              smt_ok = (uu___1716_12397.smt_ok);
                              umax_heuristic_ok =
                                (uu___1716_12397.umax_heuristic_ok);
                              tcenv = (uu___1716_12397.tcenv);
                              wl_implicits = (uu___1716_12397.wl_implicits)
                            }  in
                          solve env uu____12396))))

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
            let uu____12437 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12437 with
            | USolved wl1 ->
                let uu____12439 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12439
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12442 = defer_lit "" orig wl1  in
                solve env uu____12442

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
                  let uu____12493 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12493 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12496 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12509;
                  FStar_Syntax_Syntax.vars = uu____12510;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12513;
                  FStar_Syntax_Syntax.vars = uu____12514;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12527,uu____12528) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12536,FStar_Syntax_Syntax.Tm_uinst uu____12537) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12545 -> USolved wl

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
            ((let uu____12556 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12556
              then
                let uu____12561 = prob_to_string env orig  in
                let uu____12563 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12561 uu____12563
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
            let uu___1798_12578 = wl1  in
            let uu____12579 =
              let uu____12589 =
                let uu____12597 = FStar_Thunk.mkv reason  in
                ((wl1.ctr), uu____12597, orig)  in
              uu____12589 :: (wl1.wl_deferred_to_tac)  in
            {
              attempting = (uu___1798_12578.attempting);
              wl_deferred = (uu___1798_12578.wl_deferred);
              wl_deferred_to_tac = uu____12579;
              ctr = (uu___1798_12578.ctr);
              defer_ok = (uu___1798_12578.defer_ok);
              smt_ok = (uu___1798_12578.smt_ok);
              umax_heuristic_ok = (uu___1798_12578.umax_heuristic_ok);
              tcenv = (uu___1798_12578.tcenv);
              wl_implicits = (uu___1798_12578.wl_implicits)
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
                let uu____12626 = FStar_Syntax_Util.head_and_args t  in
                match uu____12626 with
                | (head1,uu____12650) ->
                    let uu____12675 =
                      let uu____12676 = FStar_Syntax_Subst.compress head1  in
                      uu____12676.FStar_Syntax_Syntax.n  in
                    (match uu____12675 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12686) ->
                         let uu____12703 =
                           should_defer_uvar_to_user_tac wl.tcenv uv  in
                         (uu____12703,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12707 -> (false, ""))
                 in
              let uu____12712 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs  in
              (match uu____12712 with
               | (l1,r1) ->
                   let uu____12725 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs  in
                   (match uu____12725 with
                    | (l2,r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12742 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl
                              in
                           solve env uu____12742)))
          | uu____12743 ->
              let uu____12744 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl  in
              solve env uu____12744

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
               let uu____12830 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12830 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12885 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12885
                then
                  let uu____12890 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12892 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12890 uu____12892
                else ());
               (let uu____12897 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12897 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12943 = eq_prob t1 t2 wl2  in
                         (match uu____12943 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12964 ->
                         let uu____12973 = eq_prob t1 t2 wl2  in
                         (match uu____12973 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13023 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13038 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13039 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13038, uu____13039)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13044 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13045 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13044, uu____13045)
                            in
                         (match uu____13023 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13076 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13076 with
                                | (t1_hd,t1_args) ->
                                    let uu____13121 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13121 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13187 =
                                              let uu____13194 =
                                                let uu____13205 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____13205 :: t1_args  in
                                              let uu____13222 =
                                                let uu____13231 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____13231 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____13280  ->
                                                   fun uu____13281  ->
                                                     fun uu____13282  ->
                                                       match (uu____13280,
                                                               uu____13281,
                                                               uu____13282)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____13332),
                                                          (a2,uu____13334))
                                                           ->
                                                           let uu____13371 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13371
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13194
                                                uu____13222
                                               in
                                            match uu____13187 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1901_13397 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1901_13397.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1901_13397.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1901_13397.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1901_13397.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13408 =
                                                  solve env1 wl'  in
                                                (match uu____13408 with
                                                 | Success
                                                     (uu____13411,defer_to_tac,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13415 =
                                                         extend_wl wl4
                                                           defer_to_tac imps
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13415))
                                                 | Failed uu____13416 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13448 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13448 with
                                | (t1_base,p1_opt) ->
                                    let uu____13484 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13484 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13583 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13583
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
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi11 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi1
                                                  in
                                               let phi21 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi2
                                                  in
                                               let uu____13636 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13636
                                           | (FStar_Pervasives_Native.None
                                              ,FStar_Pervasives_Native.Some
                                              (x,phi)) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13668 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13668
                                           | (FStar_Pervasives_Native.Some
                                              (x,phi),FStar_Pervasives_Native.None
                                              ) ->
                                               let x1 =
                                                 FStar_Syntax_Syntax.freshen_bv
                                                   x
                                                  in
                                               let subst1 =
                                                 [FStar_Syntax_Syntax.DB
                                                    (Prims.int_zero, x1)]
                                                  in
                                               let phi1 =
                                                 FStar_Syntax_Subst.subst
                                                   subst1 phi
                                                  in
                                               let uu____13700 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13700
                                           | uu____13703 -> t_base  in
                                         let uu____13720 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13720 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13734 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13734, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13741 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13741 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13777 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13777 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13813 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13813
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
                              let uu____13837 = combine t11 t21 wl2  in
                              (match uu____13837 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13870 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13870
                                     then
                                       let uu____13875 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13875
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13917 ts1 =
               match uu____13917 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13980 = pairwise out t wl2  in
                        (match uu____13980 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14016 =
               let uu____14027 = FStar_List.hd ts  in (uu____14027, [], wl1)
                in
             let uu____14036 = FStar_List.tl ts  in
             aux uu____14016 uu____14036  in
           let uu____14043 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14043 with
           | (this_flex,this_rigid) ->
               let uu____14069 =
                 let uu____14070 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14070.FStar_Syntax_Syntax.n  in
               (match uu____14069 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14095 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14095
                    then
                      let uu____14098 = destruct_flex_t this_flex wl  in
                      (match uu____14098 with
                       | (flex,wl1) ->
                           let uu____14105 = quasi_pattern env flex  in
                           (match uu____14105 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____14124 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14124
                                  then
                                    let uu____14129 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14129
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14136 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2011_14139 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2011_14139.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2011_14139.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2011_14139.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2011_14139.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2011_14139.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2011_14139.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2011_14139.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2011_14139.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2011_14139.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14136)
                | uu____14140 ->
                    ((let uu____14142 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14142
                      then
                        let uu____14147 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14147
                      else ());
                     (let uu____14152 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14152 with
                      | (u,_args) ->
                          let uu____14195 =
                            let uu____14196 = FStar_Syntax_Subst.compress u
                               in
                            uu____14196.FStar_Syntax_Syntax.n  in
                          (match uu____14195 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____14224 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____14224 with
                                 | (u',uu____14243) ->
                                     let uu____14268 =
                                       let uu____14269 = whnf env u'  in
                                       uu____14269.FStar_Syntax_Syntax.n  in
                                     (match uu____14268 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14291 -> false)
                                  in
                               let uu____14293 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_14316  ->
                                         match uu___26_14316 with
                                         | FStar_TypeChecker_Common.TProb tp1
                                             ->
                                             let tp2 = maybe_invert tp1  in
                                             (match tp2.FStar_TypeChecker_Common.rank
                                              with
                                              | FStar_Pervasives_Native.Some
                                                  rank' when rank1 = rank' ->
                                                  if flip
                                                  then
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.lhs
                                                  else
                                                    equiv1
                                                      tp2.FStar_TypeChecker_Common.rhs
                                              | uu____14330 -> false)
                                         | uu____14334 -> false))
                                  in
                               (match uu____14293 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14349 = whnf env this_rigid
                                         in
                                      let uu____14350 =
                                        FStar_List.collect
                                          (fun uu___27_14356  ->
                                             match uu___27_14356 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14362 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14362]
                                             | uu____14366 -> [])
                                          bounds_probs
                                         in
                                      uu____14349 :: uu____14350  in
                                    let uu____14367 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14367 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14400 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14415 =
                                               let uu____14416 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14416.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14415 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14428 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14428)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14439 -> bound  in
                                           let uu____14440 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14440)  in
                                         (match uu____14400 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14475 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14475
                                                then
                                                  let wl'1 =
                                                    let uu___2071_14481 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2071_14481.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2071_14481.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2071_14481.ctr);
                                                      defer_ok =
                                                        (uu___2071_14481.defer_ok);
                                                      smt_ok =
                                                        (uu___2071_14481.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2071_14481.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2071_14481.tcenv);
                                                      wl_implicits =
                                                        (uu___2071_14481.wl_implicits)
                                                    }  in
                                                  let uu____14482 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14482
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14488 =
                                                  solve_t env eq_prob
                                                    (let uu___2076_14490 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2076_14490.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2076_14490.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2076_14490.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2076_14490.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2076_14490.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2076_14490.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____14488 with
                                                | Success
                                                    (uu____14492,defer_to_tac,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2083_14496 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2083_14496.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2083_14496.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2083_14496.ctr);
                                                        defer_ok =
                                                          (uu___2083_14496.defer_ok);
                                                        smt_ok =
                                                          (uu___2083_14496.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2083_14496.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2083_14496.tcenv);
                                                        wl_implicits =
                                                          (uu___2083_14496.wl_implicits)
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
                                                    let uu____14513 =
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
                                                    ((let uu____14525 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14525
                                                      then
                                                        let uu____14530 =
                                                          let uu____14532 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14532
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14530
                                                      else ());
                                                     (let uu____14545 =
                                                        let uu____14560 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14560)
                                                         in
                                                      match uu____14545 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14582))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14608 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14608
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
                                                                  let uu____14628
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14628))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14653 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14653
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
                                                                    let uu____14673
                                                                    =
                                                                    let uu____14678
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14678
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14673
                                                                    [] wl2
                                                                     in
                                                                  let uu____14684
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14684))))
                                                      | uu____14685 ->
                                                          let uu____14700 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14700 p)))))))
                           | uu____14707 when flip ->
                               let uu____14708 =
                                 let uu____14710 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14712 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14710 uu____14712
                                  in
                               failwith uu____14708
                           | uu____14715 ->
                               let uu____14716 =
                                 let uu____14718 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14720 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14718 uu____14720
                                  in
                               failwith uu____14716)))))

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
                fun arrow1  ->
                  let bs_lhs_args =
                    FStar_List.map
                      (fun uu____14756  ->
                         match uu____14756 with
                         | (x,i) ->
                             let uu____14775 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14775, i)) bs_lhs
                     in
                  let uu____14778 = lhs  in
                  match uu____14778 with
                  | Flex (uu____14779,u_lhs,uu____14781) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14878 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14888 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14888, univ)
                             in
                          match uu____14878 with
                          | (k,univ) ->
                              let uu____14895 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14895 with
                               | (uu____14912,u,wl3) ->
                                   let uu____14915 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14915, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14941 =
                              let uu____14954 =
                                let uu____14965 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14965 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15016  ->
                                   fun uu____15017  ->
                                     match (uu____15016, uu____15017) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15118 =
                                           let uu____15125 =
                                             let uu____15128 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15128
                                              in
                                           copy_uvar u_lhs [] uu____15125 wl2
                                            in
                                         (match uu____15118 with
                                          | (uu____15157,t_a,wl3) ->
                                              let uu____15160 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____15160 with
                                               | (uu____15179,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14954
                                ([], wl1)
                               in
                            (match uu____14941 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2196_15235 = ct  in
                                   let uu____15236 =
                                     let uu____15239 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____15239
                                      in
                                   let uu____15254 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2196_15235.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2196_15235.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15236;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15254;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2196_15235.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2199_15272 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2199_15272.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2199_15272.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____15275 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____15275 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15313 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____15313 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15324 =
                                          let uu____15329 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15329)  in
                                        TERM uu____15324  in
                                      let uu____15330 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15330 with
                                       | (sub_prob,wl3) ->
                                           let uu____15344 =
                                             let uu____15345 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15345
                                              in
                                           solve env uu____15344))
                             | (x,imp)::formals2 ->
                                 let uu____15367 =
                                   let uu____15374 =
                                     let uu____15377 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15377
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15374 wl1
                                    in
                                 (match uu____15367 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15398 =
                                          let uu____15401 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15401
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15398 u_x
                                         in
                                      let uu____15402 =
                                        let uu____15405 =
                                          let uu____15408 =
                                            let uu____15409 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15409, imp)  in
                                          [uu____15408]  in
                                        FStar_List.append bs_terms
                                          uu____15405
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15402 formals2 wl2)
                              in
                           let uu____15436 = occurs_check u_lhs arrow1  in
                           (match uu____15436 with
                            | (uu____15449,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15465 =
                                    FStar_Thunk.mk
                                      (fun uu____15469  ->
                                         let uu____15470 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15470)
                                     in
                                  giveup_or_defer env orig wl uu____15465
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
              (let uu____15503 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15503
               then
                 let uu____15508 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15511 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15508 (rel_to_string (p_rel orig)) uu____15511
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15642 = rhs wl1 scope env1 subst1  in
                     (match uu____15642 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15665 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15665
                            then
                              let uu____15670 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15670
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15748 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15748 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2269_15750 = hd1  in
                       let uu____15751 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2269_15750.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2269_15750.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15751
                       }  in
                     let hd21 =
                       let uu___2272_15755 = hd2  in
                       let uu____15756 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2272_15755.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2272_15755.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15756
                       }  in
                     let uu____15759 =
                       let uu____15764 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15764
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15759 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15787 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15787
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15794 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15794 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15866 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15866
                                  in
                               ((let uu____15884 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15884
                                 then
                                   let uu____15889 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15891 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15889
                                     uu____15891
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15926 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15962 = aux wl [] env [] bs1 bs2  in
               match uu____15962 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16021 = attempt sub_probs wl2  in
                   solve env1 uu____16021)

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
            let uu___2310_16041 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2310_16041.wl_deferred_to_tac);
              ctr = (uu___2310_16041.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2310_16041.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16053 = try_solve env wl'  in
          match uu____16053 with
          | Success (uu____16054,defer_to_tac,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps  in solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16067 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16067 wl)

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
            let uu____16073 = should_defer_flex_to_user_tac wl lhs  in
            if uu____16073
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16086 =
                   FStar_List.map FStar_Pervasives_Native.fst bs  in
                 FStar_Util.as_set uu____16086 FStar_Syntax_Syntax.order_bv
                  in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16120 = lhs1  in
                 match uu____16120 with
                 | Flex (uu____16123,ctx_u,uu____16125) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16133 ->
                           let uu____16134 = sn_binders env1 bs  in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16134 rhs1
                        in
                     [TERM (ctx_u, sol)]
                  in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16183 = quasi_pattern env1 lhs1  in
                 match uu____16183 with
                 | FStar_Pervasives_Native.None  ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs,uu____16217) ->
                     let uu____16222 = lhs1  in
                     (match uu____16222 with
                      | Flex (t_lhs,ctx_u,args) ->
                          let uu____16237 = occurs_check ctx_u rhs1  in
                          (match uu____16237 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16288 =
                                   let uu____16296 =
                                     let uu____16298 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16298
                                      in
                                   FStar_Util.Inl uu____16296  in
                                 (uu____16288, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs)
                                     in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1
                                     in
                                  let uu____16326 =
                                    let uu____16328 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs
                                       in
                                    Prims.op_Negation uu____16328  in
                                  if uu____16326
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16355 =
                                       let uu____16363 =
                                         mk_solution env1 lhs1 bs rhs1  in
                                       FStar_Util.Inr uu____16363  in
                                     let uu____16369 =
                                       restrict_all_uvars ctx_u uvars1 wl1
                                        in
                                     (uu____16355, uu____16369)))))
                  in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16413 = FStar_Syntax_Util.head_and_args rhs1  in
                 match uu____16413 with
                 | (rhs_hd,args) ->
                     let uu____16456 = FStar_Util.prefix args  in
                     (match uu____16456 with
                      | (args_rhs,last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              FStar_Pervasives_Native.None
                              rhs1.FStar_Syntax_Syntax.pos
                             in
                          let uu____16528 = lhs1  in
                          (match uu____16528 with
                           | Flex (t_lhs,u_lhs,_lhs_args) ->
                               let uu____16532 =
                                 let uu____16543 =
                                   let uu____16550 =
                                     let uu____16553 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16553
                                      in
                                   copy_uvar u_lhs [] uu____16550 wl1  in
                                 match uu____16543 with
                                 | (uu____16580,t_last_arg,wl2) ->
                                     let uu____16583 =
                                       let uu____16590 =
                                         let uu____16591 =
                                           let uu____16600 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg
                                              in
                                           [uu____16600]  in
                                         FStar_List.append bs_lhs uu____16591
                                          in
                                       copy_uvar u_lhs uu____16590 t_res_lhs
                                         wl2
                                        in
                                     (match uu____16583 with
                                      | (uu____16635,lhs',wl3) ->
                                          let uu____16638 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3
                                             in
                                          (match uu____16638 with
                                           | (uu____16655,lhs'_last_arg,wl4)
                                               -> (lhs', lhs'_last_arg, wl4)))
                                  in
                               (match uu____16532 with
                                | (lhs',lhs'_last_arg,wl2) ->
                                    let sol =
                                      let uu____16676 =
                                        let uu____16677 =
                                          let uu____16682 =
                                            let uu____16683 =
                                              let uu____16686 =
                                                let uu____16691 =
                                                  let uu____16692 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      lhs'_last_arg
                                                     in
                                                  [uu____16692]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  lhs' uu____16691
                                                 in
                                              uu____16686
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16683
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16682)  in
                                        TERM uu____16677  in
                                      [uu____16676]  in
                                    let uu____16717 =
                                      let uu____16724 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs"
                                         in
                                      match uu____16724 with
                                      | (p1,wl3) ->
                                          let uu____16744 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs"
                                             in
                                          (match uu____16744 with
                                           | (p2,wl4) -> ([p1; p2], wl4))
                                       in
                                    (match uu____16717 with
                                     | (sub_probs,wl3) ->
                                         let uu____16776 =
                                           let uu____16777 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16777  in
                                         solve env1 uu____16776))))
                  in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16811 = FStar_Syntax_Util.head_and_args rhs2  in
                   match uu____16811 with
                   | (uu____16829,args) ->
                       (match args with | [] -> false | uu____16865 -> true)
                    in
                 let is_arrow rhs2 =
                   let uu____16884 =
                     let uu____16885 = FStar_Syntax_Subst.compress rhs2  in
                     uu____16885.FStar_Syntax_Syntax.n  in
                   match uu____16884 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____16889 -> true
                   | uu____16905 -> false  in
                 let uu____16907 = quasi_pattern env1 lhs1  in
                 match uu____16907 with
                 | FStar_Pervasives_Native.None  ->
                     let msg =
                       FStar_Thunk.mk
                         (fun uu____16925  ->
                            let uu____16926 = prob_to_string env1 orig1  in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____16926)
                        in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                     let uu____16935 = is_app rhs1  in
                     if uu____16935
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____16940 = is_arrow rhs1  in
                        if uu____16940
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             FStar_Thunk.mk
                               (fun uu____16952  ->
                                  let uu____16953 = prob_to_string env1 orig1
                                     in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____16953)
                              in
                           giveup_or_defer env1 orig1 wl1 msg))
                  in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB  ->
                   if wl.defer_ok
                   then
                     let uu____16957 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16957
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV  ->
                   if wl.defer_ok
                   then
                     let uu____16963 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16963
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ  ->
                   let uu____16968 = lhs  in
                   (match uu____16968 with
                    | Flex (_t1,ctx_uv,args_lhs) ->
                        let uu____16972 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs
                           in
                        (match uu____16972 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs  in
                             let names_to_string1 fvs =
                               let uu____16990 =
                                 let uu____16994 =
                                   FStar_Util.set_elements fvs  in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____16994
                                  in
                               FStar_All.pipe_right uu____16990
                                 (FStar_String.concat ", ")
                                in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders)
                                in
                             let fvs2 = FStar_Syntax_Free.names rhs1  in
                             let uu____17015 = occurs_check ctx_uv rhs1  in
                             (match uu____17015 with
                              | (uvars1,occurs_ok,msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17044 =
                                      let uu____17045 =
                                        let uu____17047 =
                                          FStar_Option.get msg  in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17047
                                         in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17045
                                       in
                                    giveup_or_defer env orig wl uu____17044
                                  else
                                    (let uu____17055 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1
                                        in
                                     if uu____17055
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1
                                          in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars1 wl
                                          in
                                       let uu____17062 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1
                                          in
                                       solve env uu____17062
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            FStar_Thunk.mk
                                              (fun uu____17075  ->
                                                 let uu____17076 =
                                                   names_to_string1 fvs2  in
                                                 let uu____17078 =
                                                   names_to_string1 fvs1  in
                                                 let uu____17080 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders)
                                                    in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17076 uu____17078
                                                   uu____17080)
                                             in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17092 ->
                             if wl.defer_ok
                             then
                               let uu____17096 =
                                 FStar_Thunk.mkv "Not a pattern"  in
                               giveup_or_defer env orig wl uu____17096
                             else
                               (let uu____17101 =
                                  try_quasi_pattern orig env wl lhs rhs  in
                                match uu____17101 with
                                | (FStar_Util.Inr sol,wl1) ->
                                    let uu____17127 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17127
                                | (FStar_Util.Inl msg,uu____17129) ->
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
                  let uu____17147 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17147
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____17153 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17153
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17158 =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs)
                   in
                if uu____17158
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
                    (let uu____17165 =
                       FStar_Thunk.mkv "flex-flex non-pattern"  in
                     giveup_or_defer env orig wl uu____17165)
                  else
                    (let uu____17170 =
                       let uu____17187 = quasi_pattern env lhs  in
                       let uu____17194 = quasi_pattern env rhs  in
                       (uu____17187, uu____17194)  in
                     match uu____17170 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                        (binders_rhs,t_res_rhs)) ->
                         let uu____17237 = lhs  in
                         (match uu____17237 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17238;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17240;_},u_lhs,uu____17242)
                              ->
                              let uu____17245 = rhs  in
                              (match uu____17245 with
                               | Flex (uu____17246,u_rhs,uu____17248) ->
                                   let uu____17249 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs)
                                      in
                                   if uu____17249
                                   then
                                     let uu____17256 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl
                                        in
                                     solve env uu____17256
                                   else
                                     (let uu____17259 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      match uu____17259 with
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
                                          let uu____17291 =
                                            let uu____17298 =
                                              let uu____17301 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs
                                                 in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17301
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
                                              uu____17298
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None
                                             in
                                          (match uu____17291 with
                                           | (uu____17307,w,wl1) ->
                                               let w_app =
                                                 let uu____17313 =
                                                   let uu____17318 =
                                                     FStar_List.map
                                                       (fun uu____17329  ->
                                                          match uu____17329
                                                          with
                                                          | (z,uu____17337)
                                                              ->
                                                              let uu____17342
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  z
                                                                 in
                                                              FStar_Syntax_Syntax.as_arg
                                                                uu____17342)
                                                       zs
                                                      in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     w uu____17318
                                                    in
                                                 uu____17313
                                                   FStar_Pervasives_Native.None
                                                   w.FStar_Syntax_Syntax.pos
                                                  in
                                               ((let uu____17344 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17344
                                                 then
                                                   let uu____17349 =
                                                     let uu____17353 =
                                                       flex_t_to_string lhs
                                                        in
                                                     let uu____17355 =
                                                       let uu____17359 =
                                                         flex_t_to_string rhs
                                                          in
                                                       let uu____17361 =
                                                         let uu____17365 =
                                                           term_to_string w
                                                            in
                                                         let uu____17367 =
                                                           let uu____17371 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs)
                                                              in
                                                           let uu____17380 =
                                                             let uu____17384
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                in
                                                             let uu____17393
                                                               =
                                                               let uu____17397
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs
                                                                  in
                                                               [uu____17397]
                                                                in
                                                             uu____17384 ::
                                                               uu____17393
                                                              in
                                                           uu____17371 ::
                                                             uu____17380
                                                            in
                                                         uu____17365 ::
                                                           uu____17367
                                                          in
                                                       uu____17359 ::
                                                         uu____17361
                                                        in
                                                     uu____17353 ::
                                                       uu____17355
                                                      in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17349
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17414 =
                                                       let uu____17419 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs))
                                                          in
                                                       (u_lhs, uu____17419)
                                                        in
                                                     TERM uu____17414  in
                                                   let uu____17420 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                      in
                                                   if uu____17420
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17428 =
                                                          let uu____17433 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_rhs,
                                                            uu____17433)
                                                           in
                                                        TERM uu____17428  in
                                                      [s1; s2])
                                                    in
                                                 let uu____17434 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1
                                                    in
                                                 solve env uu____17434))))))
                     | uu____17435 ->
                         let uu____17452 =
                           FStar_Thunk.mkv "flex-flex: non-patterns"  in
                         giveup_or_defer env orig wl uu____17452)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17506 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17506
            then
              let uu____17511 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17513 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17515 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17517 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17511 uu____17513 uu____17515 uu____17517
            else ());
           (let uu____17528 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17528 with
            | (head1,args1) ->
                let uu____17571 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17571 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17641 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17641 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17646 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17646)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17667 =
                         FStar_Thunk.mk
                           (fun uu____17674  ->
                              let uu____17675 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17677 = args_to_string args1  in
                              let uu____17681 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17683 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17675 uu____17677 uu____17681
                                uu____17683)
                          in
                       giveup env1 uu____17667 orig
                     else
                       (let uu____17690 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17695 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17695 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17690
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2582_17699 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2582_17699.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2582_17699.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2582_17699.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2582_17699.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2582_17699.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2582_17699.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2582_17699.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2582_17699.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17709 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17709
                                    else solve env1 wl2))
                        else
                          (let uu____17714 = base_and_refinement env1 t1  in
                           match uu____17714 with
                           | (base1,refinement1) ->
                               let uu____17739 = base_and_refinement env1 t2
                                  in
                               (match uu____17739 with
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
                                           let uu____17904 =
                                             FStar_List.fold_right
                                               (fun uu____17944  ->
                                                  fun uu____17945  ->
                                                    match (uu____17944,
                                                            uu____17945)
                                                    with
                                                    | (((a1,uu____17997),
                                                        (a2,uu____17999)),
                                                       (probs,wl3)) ->
                                                        let uu____18048 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18048
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17904 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18091 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18091
                                                 then
                                                   let uu____18096 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18096
                                                 else ());
                                                (let uu____18102 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18102
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
                                                    (let uu____18129 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18129 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18145 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18145
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18153 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18153))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18178 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18178 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18194 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18194
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18202 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18202)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18230 =
                                           match uu____18230 with
                                           | (prob,reason) ->
                                               ((let uu____18247 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18247
                                                 then
                                                   let uu____18252 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18254 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____18256 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____18252 uu____18254
                                                     uu____18256
                                                 else ());
                                                (let uu____18262 =
                                                   let uu____18271 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18274 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18271, uu____18274)
                                                    in
                                                 match uu____18262 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18287 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18287 with
                                                      | (head1',uu____18305)
                                                          ->
                                                          let uu____18330 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18330
                                                           with
                                                           | (head2',uu____18348)
                                                               ->
                                                               let uu____18373
                                                                 =
                                                                 let uu____18378
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18379
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18378,
                                                                   uu____18379)
                                                                  in
                                                               (match uu____18373
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18381
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18381
                                                                    then
                                                                    let uu____18386
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18388
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18390
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18392
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18386
                                                                    uu____18388
                                                                    uu____18390
                                                                    uu____18392
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18397
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2670_18405
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2670_18405.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2670_18405.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2670_18405.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2670_18405.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2670_18405.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2670_18405.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2670_18405.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2670_18405.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18407
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18407
                                                                    then
                                                                    let uu____18412
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18412
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18417 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18429 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18429 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18437 =
                                             let uu____18438 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18438.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18437 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18443 -> false  in
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
                                          | uu____18446 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18449 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2690_18485 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2690_18485.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2690_18485.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2690_18485.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2690_18485.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2690_18485.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2690_18485.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2690_18485.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2690_18485.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18561 = destruct_flex_t scrutinee wl1  in
             match uu____18561 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____18572 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18572 with
                  | (xs,pat_term,uu____18588,uu____18589) ->
                      let uu____18594 =
                        FStar_List.fold_left
                          (fun uu____18617  ->
                             fun x  ->
                               match uu____18617 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18638 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18638 with
                                    | (uu____18657,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18594 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18678 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18678 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2731_18695 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2731_18695.wl_deferred_to_tac);
                                    ctr = (uu___2731_18695.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2731_18695.umax_heuristic_ok);
                                    tcenv = (uu___2731_18695.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18706 = solve env1 wl'  in
                                (match uu____18706 with
                                 | Success (uu____18709,defer_to_tac,imps) ->
                                     let wl'1 =
                                       let uu___2740_18713 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2740_18713.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2740_18713.wl_deferred_to_tac);
                                         ctr = (uu___2740_18713.ctr);
                                         defer_ok =
                                           (uu___2740_18713.defer_ok);
                                         smt_ok = (uu___2740_18713.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2740_18713.umax_heuristic_ok);
                                         tcenv = (uu___2740_18713.tcenv);
                                         wl_implicits =
                                           (uu___2740_18713.wl_implicits)
                                       }  in
                                     let uu____18714 = solve env1 wl'1  in
                                     (match uu____18714 with
                                      | Success
                                          (uu____18717,defer_to_tac',imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18721 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps')
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____18721))
                                      | Failed uu____18727 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18733 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18756 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18756
                 then
                   let uu____18761 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18763 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18761 uu____18763
                 else ());
                (let uu____18768 =
                   let uu____18789 =
                     let uu____18798 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18798)  in
                   let uu____18805 =
                     let uu____18814 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18814)  in
                   (uu____18789, uu____18805)  in
                 match uu____18768 with
                 | ((uu____18844,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18847;
                                   FStar_Syntax_Syntax.vars = uu____18848;_}),
                    (s,t)) ->
                     let uu____18919 =
                       let uu____18921 = is_flex scrutinee  in
                       Prims.op_Negation uu____18921  in
                     if uu____18919
                     then
                       ((let uu____18932 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18932
                         then
                           let uu____18937 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18937
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18956 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18956
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18971 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18971
                           then
                             let uu____18976 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18978 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18976 uu____18978
                           else ());
                          (let pat_discriminates uu___28_19003 =
                             match uu___28_19003 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19019;
                                  FStar_Syntax_Syntax.p = uu____19020;_},FStar_Pervasives_Native.None
                                ,uu____19021) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19035;
                                  FStar_Syntax_Syntax.p = uu____19036;_},FStar_Pervasives_Native.None
                                ,uu____19037) -> true
                             | uu____19064 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19167 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19167 with
                                       | (uu____19169,uu____19170,t') ->
                                           let uu____19188 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19188 with
                                            | (FullMatch ,uu____19200) ->
                                                true
                                            | (HeadMatch
                                               uu____19214,uu____19215) ->
                                                true
                                            | uu____19230 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19267 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19267
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19278 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19278 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19366,uu____19367) ->
                                       branches1
                                   | uu____19512 -> branches  in
                                 let uu____19567 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19576 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19576 with
                                        | (p,uu____19580,uu____19581) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19610  -> FStar_Util.Inr _19610)
                                   uu____19567))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19640 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19640 with
                                | (p,uu____19649,e) ->
                                    ((let uu____19668 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19668
                                      then
                                        let uu____19673 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19675 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19673 uu____19675
                                      else ());
                                     (let uu____19680 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19695  -> FStar_Util.Inr _19695)
                                        uu____19680)))))
                 | ((s,t),(uu____19698,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19701;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19702;_}))
                     ->
                     let uu____19771 =
                       let uu____19773 = is_flex scrutinee  in
                       Prims.op_Negation uu____19773  in
                     if uu____19771
                     then
                       ((let uu____19784 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19784
                         then
                           let uu____19789 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19789
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19808 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19808
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19823 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19823
                           then
                             let uu____19828 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19830 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19828 uu____19830
                           else ());
                          (let pat_discriminates uu___28_19855 =
                             match uu___28_19855 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19871;
                                  FStar_Syntax_Syntax.p = uu____19872;_},FStar_Pervasives_Native.None
                                ,uu____19873) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19887;
                                  FStar_Syntax_Syntax.p = uu____19888;_},FStar_Pervasives_Native.None
                                ,uu____19889) -> true
                             | uu____19916 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20019 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20019 with
                                       | (uu____20021,uu____20022,t') ->
                                           let uu____20040 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20040 with
                                            | (FullMatch ,uu____20052) ->
                                                true
                                            | (HeadMatch
                                               uu____20066,uu____20067) ->
                                                true
                                            | uu____20082 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20119 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20119
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20130 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20130 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20218,uu____20219) ->
                                       branches1
                                   | uu____20364 -> branches  in
                                 let uu____20419 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20428 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20428 with
                                        | (p,uu____20432,uu____20433) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _20462  -> FStar_Util.Inr _20462)
                                   uu____20419))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20492 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20492 with
                                | (p,uu____20501,e) ->
                                    ((let uu____20520 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20520
                                      then
                                        let uu____20525 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20527 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20525 uu____20527
                                      else ());
                                     (let uu____20532 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _20547  -> FStar_Util.Inr _20547)
                                        uu____20532)))))
                 | uu____20548 ->
                     ((let uu____20570 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20570
                       then
                         let uu____20575 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20577 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20575 uu____20577
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20623 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20623
            then
              let uu____20628 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20630 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20632 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20634 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20628 uu____20630 uu____20632 uu____20634
            else ());
           (let uu____20639 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20639 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20670,uu____20671) ->
                     let rec may_relate head3 =
                       let uu____20699 =
                         let uu____20700 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20700.FStar_Syntax_Syntax.n  in
                       match uu____20699 with
                       | FStar_Syntax_Syntax.Tm_name uu____20704 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20706 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20731 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20731 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20733 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20736
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20737 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20740,uu____20741) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20783) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20789) ->
                           may_relate t
                       | uu____20794 -> false  in
                     let uu____20796 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20796 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20809 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20809
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20819 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20819
                          then
                            let uu____20822 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20822 with
                             | (guard,wl2) ->
                                 let uu____20829 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20829)
                          else
                            (let uu____20832 =
                               FStar_Thunk.mk
                                 (fun uu____20839  ->
                                    let uu____20840 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20842 =
                                      let uu____20844 =
                                        let uu____20848 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20848
                                          (fun x  ->
                                             let uu____20855 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20855)
                                         in
                                      FStar_Util.dflt "" uu____20844  in
                                    let uu____20860 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20862 =
                                      let uu____20864 =
                                        let uu____20868 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20868
                                          (fun x  ->
                                             let uu____20875 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20875)
                                         in
                                      FStar_Util.dflt "" uu____20864  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20840 uu____20842 uu____20860
                                      uu____20862)
                                in
                             giveup env1 uu____20832 orig))
                 | (HeadMatch (true ),uu____20881) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20896 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20896 with
                        | (guard,wl2) ->
                            let uu____20903 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20903)
                     else
                       (let uu____20906 =
                          FStar_Thunk.mk
                            (fun uu____20911  ->
                               let uu____20912 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20914 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20912 uu____20914)
                           in
                        giveup env1 uu____20906 orig)
                 | (uu____20917,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2922_20931 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2922_20931.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2922_20931.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2922_20931.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2922_20931.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2922_20931.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2922_20931.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2922_20931.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2922_20931.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20958 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20958
          then
            let uu____20961 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20961
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20967 =
                let uu____20970 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20970  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20967 t1);
             (let uu____20989 =
                let uu____20992 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20992  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20989 t2);
             (let uu____21011 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____21011
              then
                let uu____21015 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____21017 =
                  let uu____21019 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____21021 =
                    let uu____21023 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____21023  in
                  Prims.op_Hat uu____21019 uu____21021  in
                let uu____21026 =
                  let uu____21028 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____21030 =
                    let uu____21032 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____21032  in
                  Prims.op_Hat uu____21028 uu____21030  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21015 uu____21017 uu____21026
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21039,uu____21040) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21056,FStar_Syntax_Syntax.Tm_delayed uu____21057) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21073,uu____21074) ->
                  let uu____21101 =
                    let uu___2953_21102 = problem  in
                    let uu____21103 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2953_21102.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21103;
                      FStar_TypeChecker_Common.relation =
                        (uu___2953_21102.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2953_21102.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2953_21102.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2953_21102.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2953_21102.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2953_21102.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2953_21102.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2953_21102.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21101 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21104,uu____21105) ->
                  let uu____21112 =
                    let uu___2959_21113 = problem  in
                    let uu____21114 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2959_21113.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21114;
                      FStar_TypeChecker_Common.relation =
                        (uu___2959_21113.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2959_21113.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2959_21113.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2959_21113.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2959_21113.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2959_21113.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2959_21113.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2959_21113.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21112 wl
              | (uu____21115,FStar_Syntax_Syntax.Tm_ascribed uu____21116) ->
                  let uu____21143 =
                    let uu___2965_21144 = problem  in
                    let uu____21145 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2965_21144.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2965_21144.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2965_21144.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21145;
                      FStar_TypeChecker_Common.element =
                        (uu___2965_21144.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2965_21144.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2965_21144.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2965_21144.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2965_21144.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2965_21144.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21143 wl
              | (uu____21146,FStar_Syntax_Syntax.Tm_meta uu____21147) ->
                  let uu____21154 =
                    let uu___2971_21155 = problem  in
                    let uu____21156 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2971_21155.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2971_21155.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2971_21155.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21156;
                      FStar_TypeChecker_Common.element =
                        (uu___2971_21155.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2971_21155.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2971_21155.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2971_21155.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2971_21155.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2971_21155.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21154 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21158),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21160)) ->
                  let uu____21169 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21169
              | (FStar_Syntax_Syntax.Tm_bvar uu____21170,uu____21171) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21173,FStar_Syntax_Syntax.Tm_bvar uu____21174) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_21244 =
                    match uu___29_21244 with
                    | [] -> c
                    | bs ->
                        let uu____21272 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21272
                     in
                  let uu____21283 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21283 with
                   | ((bs11,c11),(bs21,c21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let c12 =
                                    FStar_Syntax_Subst.subst_comp subst1 c11
                                     in
                                  let c22 =
                                    FStar_Syntax_Subst.subst_comp subst1 c21
                                     in
                                  let rel =
                                    let uu____21432 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21432
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
                  let mk_t t l uu___30_21521 =
                    match uu___30_21521 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21563 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21563 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21708 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21709 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21708
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21709 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21711,uu____21712) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21743 -> true
                    | uu____21763 -> false  in
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
                      (let uu____21823 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3073_21831 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3073_21831.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3073_21831.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3073_21831.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3073_21831.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3073_21831.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3073_21831.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3073_21831.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3073_21831.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3073_21831.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3073_21831.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3073_21831.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3073_21831.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3073_21831.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3073_21831.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3073_21831.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3073_21831.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3073_21831.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3073_21831.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3073_21831.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3073_21831.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3073_21831.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3073_21831.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3073_21831.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3073_21831.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3073_21831.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3073_21831.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3073_21831.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3073_21831.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3073_21831.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3073_21831.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3073_21831.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3073_21831.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3073_21831.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3073_21831.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3073_21831.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3073_21831.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3073_21831.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3073_21831.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3073_21831.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3073_21831.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3073_21831.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3073_21831.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3073_21831.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3073_21831.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3073_21831.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____21823 with
                       | (uu____21836,ty,uu____21838) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21847 =
                                 let uu____21848 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21848.FStar_Syntax_Syntax.n  in
                               match uu____21847 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21851 ->
                                   let uu____21858 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21858
                               | uu____21859 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21862 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21862
                             then
                               let uu____21867 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21869 =
                                 let uu____21871 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21871
                                  in
                               let uu____21872 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21867 uu____21869 uu____21872
                             else ());
                            r1))
                     in
                  let uu____21877 =
                    let uu____21894 = maybe_eta t1  in
                    let uu____21901 = maybe_eta t2  in
                    (uu____21894, uu____21901)  in
                  (match uu____21877 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3094_21943 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3094_21943.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3094_21943.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3094_21943.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3094_21943.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3094_21943.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3094_21943.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3094_21943.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3094_21943.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21964 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21964
                       then
                         let uu____21967 = destruct_flex_t not_abs wl  in
                         (match uu____21967 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_21984 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_21984.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_21984.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_21984.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_21984.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_21984.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_21984.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_21984.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_21984.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21987 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21987 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22010 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22010
                       then
                         let uu____22013 = destruct_flex_t not_abs wl  in
                         (match uu____22013 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_22030 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_22030.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_22030.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_22030.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_22030.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_22030.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_22030.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_22030.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_22030.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22033 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22033 orig))
                   | uu____22036 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22054,FStar_Syntax_Syntax.Tm_abs uu____22055) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22086 -> true
                    | uu____22106 -> false  in
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
                      (let uu____22166 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3073_22174 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3073_22174.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3073_22174.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3073_22174.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3073_22174.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3073_22174.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3073_22174.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3073_22174.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3073_22174.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3073_22174.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3073_22174.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3073_22174.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3073_22174.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3073_22174.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3073_22174.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3073_22174.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3073_22174.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3073_22174.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3073_22174.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3073_22174.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3073_22174.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3073_22174.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3073_22174.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3073_22174.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3073_22174.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3073_22174.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3073_22174.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3073_22174.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3073_22174.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3073_22174.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3073_22174.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3073_22174.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3073_22174.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3073_22174.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3073_22174.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3073_22174.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3073_22174.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3073_22174.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3073_22174.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3073_22174.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3073_22174.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3073_22174.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3073_22174.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3073_22174.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3073_22174.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3073_22174.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____22166 with
                       | (uu____22179,ty,uu____22181) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22190 =
                                 let uu____22191 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22191.FStar_Syntax_Syntax.n  in
                               match uu____22190 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22194 ->
                                   let uu____22201 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22201
                               | uu____22202 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22205 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22205
                             then
                               let uu____22210 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22212 =
                                 let uu____22214 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22214
                                  in
                               let uu____22215 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22210 uu____22212 uu____22215
                             else ());
                            r1))
                     in
                  let uu____22220 =
                    let uu____22237 = maybe_eta t1  in
                    let uu____22244 = maybe_eta t2  in
                    (uu____22237, uu____22244)  in
                  (match uu____22220 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3094_22286 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3094_22286.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3094_22286.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3094_22286.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3094_22286.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3094_22286.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3094_22286.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3094_22286.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3094_22286.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22307 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22307
                       then
                         let uu____22310 = destruct_flex_t not_abs wl  in
                         (match uu____22310 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_22327 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_22327.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_22327.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_22327.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_22327.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_22327.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_22327.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_22327.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_22327.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22330 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22330 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22353 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22353
                       then
                         let uu____22356 = destruct_flex_t not_abs wl  in
                         (match uu____22356 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_22373 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_22373.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_22373.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_22373.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_22373.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_22373.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_22373.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_22373.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_22373.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22376 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22376 orig))
                   | uu____22379 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22409 =
                    let uu____22414 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22414 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3134_22442 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3134_22442.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3134_22442.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3136_22444 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3136_22444.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3136_22444.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22445,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3134_22460 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3134_22460.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3134_22460.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3136_22462 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3136_22462.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3136_22462.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22463 -> (x1, x2)  in
                  (match uu____22409 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22482 = as_refinement false env t11  in
                       (match uu____22482 with
                        | (x12,phi11) ->
                            let uu____22490 = as_refinement false env t21  in
                            (match uu____22490 with
                             | (x22,phi21) ->
                                 ((let uu____22499 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22499
                                   then
                                     ((let uu____22504 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22506 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22508 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22504
                                         uu____22506 uu____22508);
                                      (let uu____22511 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22513 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22515 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22511
                                         uu____22513 uu____22515))
                                   else ());
                                  (let uu____22520 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22520 with
                                   | (base_prob,wl1) ->
                                       let x13 =
                                         FStar_Syntax_Syntax.freshen_bv x12
                                          in
                                       let subst1 =
                                         [FStar_Syntax_Syntax.DB
                                            (Prims.int_zero, x13)]
                                          in
                                       let phi12 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi11
                                          in
                                       let phi22 =
                                         FStar_Syntax_Subst.subst subst1
                                           phi21
                                          in
                                       let env1 =
                                         FStar_TypeChecker_Env.push_bv env
                                           x13
                                          in
                                       let mk_imp1 imp phi13 phi23 =
                                         let uu____22591 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22591
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22603 =
                                         let impl =
                                           if
                                             problem.FStar_TypeChecker_Common.relation
                                               = FStar_TypeChecker_Common.EQ
                                           then
                                             mk_imp1 FStar_Syntax_Util.mk_iff
                                               phi12 phi22
                                           else
                                             mk_imp1 FStar_Syntax_Util.mk_imp
                                               phi12 phi22
                                            in
                                         let guard =
                                           FStar_Syntax_Util.mk_conj
                                             (p_guard base_prob) impl
                                            in
                                         (let uu____22616 =
                                            let uu____22619 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22619
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22616
                                            (p_guard base_prob));
                                         (let uu____22638 =
                                            let uu____22641 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22641
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22638
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22660 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22660)
                                          in
                                       let has_uvars =
                                         (let uu____22665 =
                                            let uu____22667 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22667
                                             in
                                          Prims.op_Negation uu____22665) ||
                                           (let uu____22671 =
                                              let uu____22673 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22673
                                               in
                                            Prims.op_Negation uu____22671)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22677 =
                                           let uu____22682 =
                                             let uu____22691 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22691]  in
                                           mk_t_problem wl1 uu____22682 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22677 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22714 =
                                                solve env1
                                                  (let uu___3179_22716 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3179_22716.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3179_22716.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3179_22716.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3179_22716.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3179_22716.tcenv);
                                                     wl_implicits =
                                                       (uu___3179_22716.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22714 with
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
                                                   (uu____22731,defer_to_tac,uu____22733)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22738 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22738
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3195_22747 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3195_22747.attempting);
                                                         wl_deferred =
                                                           (uu___3195_22747.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3195_22747.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3195_22747.defer_ok);
                                                         smt_ok =
                                                           (uu___3195_22747.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3195_22747.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3195_22747.tcenv);
                                                         wl_implicits =
                                                           (uu___3195_22747.wl_implicits)
                                                       }  in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac []
                                                        in
                                                     let uu____22750 =
                                                       attempt [base_prob]
                                                         wl5
                                                        in
                                                     solve env1 uu____22750))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22753,FStar_Syntax_Syntax.Tm_uvar uu____22754) ->
                  let uu____22779 = destruct_flex_t t1 wl  in
                  (match uu____22779 with
                   | (f1,wl1) ->
                       let uu____22786 = destruct_flex_t t2 wl1  in
                       (match uu____22786 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22793;
                    FStar_Syntax_Syntax.pos = uu____22794;
                    FStar_Syntax_Syntax.vars = uu____22795;_},uu____22796),FStar_Syntax_Syntax.Tm_uvar
                 uu____22797) ->
                  let uu____22846 = destruct_flex_t t1 wl  in
                  (match uu____22846 with
                   | (f1,wl1) ->
                       let uu____22853 = destruct_flex_t t2 wl1  in
                       (match uu____22853 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22860,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22861;
                    FStar_Syntax_Syntax.pos = uu____22862;
                    FStar_Syntax_Syntax.vars = uu____22863;_},uu____22864))
                  ->
                  let uu____22913 = destruct_flex_t t1 wl  in
                  (match uu____22913 with
                   | (f1,wl1) ->
                       let uu____22920 = destruct_flex_t t2 wl1  in
                       (match uu____22920 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22927;
                    FStar_Syntax_Syntax.pos = uu____22928;
                    FStar_Syntax_Syntax.vars = uu____22929;_},uu____22930),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22931;
                    FStar_Syntax_Syntax.pos = uu____22932;
                    FStar_Syntax_Syntax.vars = uu____22933;_},uu____22934))
                  ->
                  let uu____23007 = destruct_flex_t t1 wl  in
                  (match uu____23007 with
                   | (f1,wl1) ->
                       let uu____23014 = destruct_flex_t t2 wl1  in
                       (match uu____23014 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23021,uu____23022) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23035 = destruct_flex_t t1 wl  in
                  (match uu____23035 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23042;
                    FStar_Syntax_Syntax.pos = uu____23043;
                    FStar_Syntax_Syntax.vars = uu____23044;_},uu____23045),uu____23046)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23083 = destruct_flex_t t1 wl  in
                  (match uu____23083 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23090,FStar_Syntax_Syntax.Tm_uvar uu____23091) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23104,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23105;
                    FStar_Syntax_Syntax.pos = uu____23106;
                    FStar_Syntax_Syntax.vars = uu____23107;_},uu____23108))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23145,FStar_Syntax_Syntax.Tm_arrow uu____23146) ->
                  solve_t' env
                    (let uu___3296_23174 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3296_23174.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3296_23174.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3296_23174.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3296_23174.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3296_23174.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3296_23174.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3296_23174.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3296_23174.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3296_23174.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23175;
                    FStar_Syntax_Syntax.pos = uu____23176;
                    FStar_Syntax_Syntax.vars = uu____23177;_},uu____23178),FStar_Syntax_Syntax.Tm_arrow
                 uu____23179) ->
                  solve_t' env
                    (let uu___3296_23231 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3296_23231.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3296_23231.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3296_23231.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3296_23231.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3296_23231.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3296_23231.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3296_23231.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3296_23231.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3296_23231.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23232,FStar_Syntax_Syntax.Tm_uvar uu____23233) ->
                  let uu____23246 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23246
              | (uu____23247,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23248;
                    FStar_Syntax_Syntax.pos = uu____23249;
                    FStar_Syntax_Syntax.vars = uu____23250;_},uu____23251))
                  ->
                  let uu____23288 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23288
              | (FStar_Syntax_Syntax.Tm_uvar uu____23289,uu____23290) ->
                  let uu____23303 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23303
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23304;
                    FStar_Syntax_Syntax.pos = uu____23305;
                    FStar_Syntax_Syntax.vars = uu____23306;_},uu____23307),uu____23308)
                  ->
                  let uu____23345 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23345
              | (FStar_Syntax_Syntax.Tm_refine uu____23346,uu____23347) ->
                  let t21 =
                    let uu____23355 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23355  in
                  solve_t env
                    (let uu___3331_23381 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3331_23381.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3331_23381.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3331_23381.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3331_23381.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3331_23381.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3331_23381.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3331_23381.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3331_23381.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3331_23381.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23382,FStar_Syntax_Syntax.Tm_refine uu____23383) ->
                  let t11 =
                    let uu____23391 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23391  in
                  solve_t env
                    (let uu___3338_23417 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3338_23417.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3338_23417.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3338_23417.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3338_23417.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3338_23417.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3338_23417.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3338_23417.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3338_23417.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3338_23417.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23499 =
                    let uu____23500 = guard_of_prob env wl problem t1 t2  in
                    match uu____23500 with
                    | (guard,wl1) ->
                        let uu____23507 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23507
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23726 = br1  in
                        (match uu____23726 with
                         | (p1,w1,uu____23755) ->
                             let uu____23772 = br2  in
                             (match uu____23772 with
                              | (p2,w2,uu____23795) ->
                                  let uu____23800 =
                                    let uu____23802 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23802  in
                                  if uu____23800
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23829 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23829 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23866 = br2  in
                                         (match uu____23866 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23899 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23899
                                                 in
                                              let uu____23904 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23935,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23956) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____24015 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____24015 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23904
                                                (fun uu____24087  ->
                                                   match uu____24087 with
                                                   | (wprobs,wl2) ->
                                                       let uu____24124 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____24124
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24145
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24145
                                                              then
                                                                let uu____24150
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24152
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24150
                                                                  uu____24152
                                                              else ());
                                                             (let uu____24158
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24158
                                                                (fun
                                                                   uu____24194
                                                                    ->
                                                                   match uu____24194
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
                    | uu____24323 -> FStar_Pervasives_Native.None  in
                  let uu____24364 = solve_branches wl brs1 brs2  in
                  (match uu____24364 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24390 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24390 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24417 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24417 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24451 =
                                FStar_List.map
                                  (fun uu____24463  ->
                                     match uu____24463 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24451  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24472 =
                              let uu____24473 =
                                let uu____24474 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24474
                                  (let uu___3437_24482 = wl3  in
                                   {
                                     attempting =
                                       (uu___3437_24482.attempting);
                                     wl_deferred =
                                       (uu___3437_24482.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3437_24482.wl_deferred_to_tac);
                                     ctr = (uu___3437_24482.ctr);
                                     defer_ok = (uu___3437_24482.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3437_24482.umax_heuristic_ok);
                                     tcenv = (uu___3437_24482.tcenv);
                                     wl_implicits =
                                       (uu___3437_24482.wl_implicits)
                                   })
                                 in
                              solve env uu____24473  in
                            (match uu____24472 with
                             | Success (ds,ds',imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24488 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24497 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24497 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24500,uu____24501) ->
                  let head1 =
                    let uu____24525 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24525
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24571 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24571
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24617 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24617
                    then
                      let uu____24621 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24623 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24625 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24621 uu____24623 uu____24625
                    else ());
                   (let no_free_uvars t =
                      (let uu____24639 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24639) &&
                        (let uu____24643 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24643)
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
                      let uu____24662 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24662 = FStar_Syntax_Util.Equal  in
                    let uu____24663 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24663
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24667 = equal t1 t2  in
                         (if uu____24667
                          then
                            let uu____24670 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24670
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24675 =
                            let uu____24682 = equal t1 t2  in
                            if uu____24682
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24695 = mk_eq2 wl env orig t1 t2  in
                               match uu____24695 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24675 with
                          | (guard,wl1) ->
                              let uu____24716 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24716))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24719,uu____24720) ->
                  let head1 =
                    let uu____24728 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24728
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24774 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24774
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24820 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24820
                    then
                      let uu____24824 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24826 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24828 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24824 uu____24826 uu____24828
                    else ());
                   (let no_free_uvars t =
                      (let uu____24842 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24842) &&
                        (let uu____24846 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24846)
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
                      let uu____24865 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24865 = FStar_Syntax_Util.Equal  in
                    let uu____24866 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24866
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24870 = equal t1 t2  in
                         (if uu____24870
                          then
                            let uu____24873 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24873
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24878 =
                            let uu____24885 = equal t1 t2  in
                            if uu____24885
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24898 = mk_eq2 wl env orig t1 t2  in
                               match uu____24898 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24878 with
                          | (guard,wl1) ->
                              let uu____24919 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24919))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24922,uu____24923) ->
                  let head1 =
                    let uu____24925 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24925
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24971 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24971
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25017 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25017
                    then
                      let uu____25021 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25023 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25025 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25021 uu____25023 uu____25025
                    else ());
                   (let no_free_uvars t =
                      (let uu____25039 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25039) &&
                        (let uu____25043 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25043)
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
                      let uu____25062 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25062 = FStar_Syntax_Util.Equal  in
                    let uu____25063 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25063
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25067 = equal t1 t2  in
                         (if uu____25067
                          then
                            let uu____25070 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25070
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25075 =
                            let uu____25082 = equal t1 t2  in
                            if uu____25082
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25095 = mk_eq2 wl env orig t1 t2  in
                               match uu____25095 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25075 with
                          | (guard,wl1) ->
                              let uu____25116 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25116))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25119,uu____25120) ->
                  let head1 =
                    let uu____25122 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25122
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25168 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25168
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25214 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25214
                    then
                      let uu____25218 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25220 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25222 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25218 uu____25220 uu____25222
                    else ());
                   (let no_free_uvars t =
                      (let uu____25236 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25236) &&
                        (let uu____25240 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25240)
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
                      let uu____25259 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25259 = FStar_Syntax_Util.Equal  in
                    let uu____25260 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25260
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25264 = equal t1 t2  in
                         (if uu____25264
                          then
                            let uu____25267 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25267
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25272 =
                            let uu____25279 = equal t1 t2  in
                            if uu____25279
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25292 = mk_eq2 wl env orig t1 t2  in
                               match uu____25292 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25272 with
                          | (guard,wl1) ->
                              let uu____25313 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25313))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25316,uu____25317) ->
                  let head1 =
                    let uu____25319 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25319
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25359 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25359
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25399 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25399
                    then
                      let uu____25403 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25405 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25407 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25403 uu____25405 uu____25407
                    else ());
                   (let no_free_uvars t =
                      (let uu____25421 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25421) &&
                        (let uu____25425 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25425)
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
                      let uu____25444 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25444 = FStar_Syntax_Util.Equal  in
                    let uu____25445 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25445
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25449 = equal t1 t2  in
                         (if uu____25449
                          then
                            let uu____25452 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25452
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25457 =
                            let uu____25464 = equal t1 t2  in
                            if uu____25464
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25477 = mk_eq2 wl env orig t1 t2  in
                               match uu____25477 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25457 with
                          | (guard,wl1) ->
                              let uu____25498 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25498))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25501,uu____25502) ->
                  let head1 =
                    let uu____25520 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25520
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25560 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25560
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25600 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25600
                    then
                      let uu____25604 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25606 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25608 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25604 uu____25606 uu____25608
                    else ());
                   (let no_free_uvars t =
                      (let uu____25622 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25622) &&
                        (let uu____25626 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25626)
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
                      let uu____25645 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25645 = FStar_Syntax_Util.Equal  in
                    let uu____25646 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25646
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25650 = equal t1 t2  in
                         (if uu____25650
                          then
                            let uu____25653 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25653
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25658 =
                            let uu____25665 = equal t1 t2  in
                            if uu____25665
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25678 = mk_eq2 wl env orig t1 t2  in
                               match uu____25678 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25658 with
                          | (guard,wl1) ->
                              let uu____25699 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25699))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25702,FStar_Syntax_Syntax.Tm_match uu____25703) ->
                  let head1 =
                    let uu____25727 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25727
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25767 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25767
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25807 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25807
                    then
                      let uu____25811 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25813 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25815 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25811 uu____25813 uu____25815
                    else ());
                   (let no_free_uvars t =
                      (let uu____25829 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25829) &&
                        (let uu____25833 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25833)
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
                      let uu____25852 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25852 = FStar_Syntax_Util.Equal  in
                    let uu____25853 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25853
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25857 = equal t1 t2  in
                         (if uu____25857
                          then
                            let uu____25860 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25860
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25865 =
                            let uu____25872 = equal t1 t2  in
                            if uu____25872
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25885 = mk_eq2 wl env orig t1 t2  in
                               match uu____25885 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25865 with
                          | (guard,wl1) ->
                              let uu____25906 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25906))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25909,FStar_Syntax_Syntax.Tm_uinst uu____25910) ->
                  let head1 =
                    let uu____25918 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25918
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25958 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25958
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25998 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25998
                    then
                      let uu____26002 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26004 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26006 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26002 uu____26004 uu____26006
                    else ());
                   (let no_free_uvars t =
                      (let uu____26020 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26020) &&
                        (let uu____26024 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26024)
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
                      let uu____26043 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26043 = FStar_Syntax_Util.Equal  in
                    let uu____26044 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26044
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26048 = equal t1 t2  in
                         (if uu____26048
                          then
                            let uu____26051 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26051
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26056 =
                            let uu____26063 = equal t1 t2  in
                            if uu____26063
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26076 = mk_eq2 wl env orig t1 t2  in
                               match uu____26076 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26056 with
                          | (guard,wl1) ->
                              let uu____26097 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26097))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26100,FStar_Syntax_Syntax.Tm_name uu____26101) ->
                  let head1 =
                    let uu____26103 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26103
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26143 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26143
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26183 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26183
                    then
                      let uu____26187 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26189 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26191 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26187 uu____26189 uu____26191
                    else ());
                   (let no_free_uvars t =
                      (let uu____26205 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26205) &&
                        (let uu____26209 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26209)
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
                      let uu____26228 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26228 = FStar_Syntax_Util.Equal  in
                    let uu____26229 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26229
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26233 = equal t1 t2  in
                         (if uu____26233
                          then
                            let uu____26236 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26236
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26241 =
                            let uu____26248 = equal t1 t2  in
                            if uu____26248
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26261 = mk_eq2 wl env orig t1 t2  in
                               match uu____26261 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26241 with
                          | (guard,wl1) ->
                              let uu____26282 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26282))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26285,FStar_Syntax_Syntax.Tm_constant uu____26286) ->
                  let head1 =
                    let uu____26288 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26288
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26328 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26328
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26368 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26368
                    then
                      let uu____26372 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26374 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26376 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26372 uu____26374 uu____26376
                    else ());
                   (let no_free_uvars t =
                      (let uu____26390 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26390) &&
                        (let uu____26394 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26394)
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
                      let uu____26413 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26413 = FStar_Syntax_Util.Equal  in
                    let uu____26414 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26414
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26418 = equal t1 t2  in
                         (if uu____26418
                          then
                            let uu____26421 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26421
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26426 =
                            let uu____26433 = equal t1 t2  in
                            if uu____26433
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26446 = mk_eq2 wl env orig t1 t2  in
                               match uu____26446 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26426 with
                          | (guard,wl1) ->
                              let uu____26467 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26467))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26470,FStar_Syntax_Syntax.Tm_fvar uu____26471) ->
                  let head1 =
                    let uu____26473 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26473
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26519 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26519
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26565 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26565
                    then
                      let uu____26569 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26571 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26573 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26569 uu____26571 uu____26573
                    else ());
                   (let no_free_uvars t =
                      (let uu____26587 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26587) &&
                        (let uu____26591 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26591)
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
                      let uu____26610 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26610 = FStar_Syntax_Util.Equal  in
                    let uu____26611 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26611
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26615 = equal t1 t2  in
                         (if uu____26615
                          then
                            let uu____26618 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26618
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26623 =
                            let uu____26630 = equal t1 t2  in
                            if uu____26630
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26643 = mk_eq2 wl env orig t1 t2  in
                               match uu____26643 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26623 with
                          | (guard,wl1) ->
                              let uu____26664 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26664))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26667,FStar_Syntax_Syntax.Tm_app uu____26668) ->
                  let head1 =
                    let uu____26686 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26686
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26726 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26726
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26766 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26766
                    then
                      let uu____26770 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26772 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26774 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26770 uu____26772 uu____26774
                    else ());
                   (let no_free_uvars t =
                      (let uu____26788 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26788) &&
                        (let uu____26792 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26792)
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
                      let uu____26811 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26811 = FStar_Syntax_Util.Equal  in
                    let uu____26812 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26812
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26816 = equal t1 t2  in
                         (if uu____26816
                          then
                            let uu____26819 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26819
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26824 =
                            let uu____26831 = equal t1 t2  in
                            if uu____26831
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26844 = mk_eq2 wl env orig t1 t2  in
                               match uu____26844 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26824 with
                          | (guard,wl1) ->
                              let uu____26865 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26865))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26868,FStar_Syntax_Syntax.Tm_let uu____26869) ->
                  let uu____26896 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26896
                  then
                    let uu____26899 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26899
                  else
                    (let uu____26902 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26902 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26905,uu____26906) ->
                  let uu____26920 =
                    let uu____26926 =
                      let uu____26928 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26930 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26932 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26934 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26928 uu____26930 uu____26932 uu____26934
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26926)
                     in
                  FStar_Errors.raise_error uu____26920
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26938,FStar_Syntax_Syntax.Tm_let uu____26939) ->
                  let uu____26953 =
                    let uu____26959 =
                      let uu____26961 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26963 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26965 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26967 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26961 uu____26963 uu____26965 uu____26967
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26959)
                     in
                  FStar_Errors.raise_error uu____26953
                    t1.FStar_Syntax_Syntax.pos
              | uu____26971 ->
                  let uu____26976 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26976 orig))))

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
          (let uu____27042 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____27042
           then
             let uu____27047 =
               let uu____27049 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____27049  in
             let uu____27050 =
               let uu____27052 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____27052  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27047 uu____27050
           else ());
          (let uu____27056 =
             let uu____27058 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____27058  in
           if uu____27056
           then
             let uu____27061 =
               FStar_Thunk.mk
                 (fun uu____27066  ->
                    let uu____27067 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____27069 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27067 uu____27069)
                in
             giveup env uu____27061 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27091 =
                  FStar_Thunk.mk
                    (fun uu____27096  ->
                       let uu____27097 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27099 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27097 uu____27099)
                   in
                giveup env uu____27091 orig)
             else
               (let uu____27104 =
                  FStar_List.fold_left2
                    (fun uu____27125  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27125 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27146 =
                                 let uu____27151 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27152 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27151
                                   FStar_TypeChecker_Common.EQ uu____27152
                                   "effect universes"
                                  in
                               (match uu____27146 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27104 with
                | (univ_sub_probs,wl1) ->
                    let uu____27172 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27172 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27180 =
                           FStar_List.fold_right2
                             (fun uu____27217  ->
                                fun uu____27218  ->
                                  fun uu____27219  ->
                                    match (uu____27217, uu____27218,
                                            uu____27219)
                                    with
                                    | ((a1,uu____27263),(a2,uu____27265),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27298 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27298 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27180 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27325 =
                                  let uu____27328 =
                                    let uu____27331 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27331
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27328
                                   in
                                FStar_List.append univ_sub_probs uu____27325
                                 in
                              let guard =
                                let guard =
                                  let uu____27353 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27353  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3590_27362 = wl3  in
                                {
                                  attempting = (uu___3590_27362.attempting);
                                  wl_deferred = (uu___3590_27362.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3590_27362.wl_deferred_to_tac);
                                  ctr = (uu___3590_27362.ctr);
                                  defer_ok = (uu___3590_27362.defer_ok);
                                  smt_ok = (uu___3590_27362.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3590_27362.umax_heuristic_ok);
                                  tcenv = (uu___3590_27362.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27364 = attempt sub_probs wl5  in
                              solve env uu____27364))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____27382 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____27382
           then
             let uu____27387 =
               let uu____27389 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27389
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27391 =
               let uu____27393 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27393
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27387 uu____27391
           else ());
          (let uu____27398 =
             let uu____27403 =
               let uu____27408 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27408
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27403
               (fun uu____27425  ->
                  match uu____27425 with
                  | (c,g) ->
                      let uu____27436 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27436, g))
              in
           match uu____27398 with
           | (c12,g_lift) ->
               ((let uu____27440 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27440
                 then
                   let uu____27445 =
                     let uu____27447 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27447
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27449 =
                     let uu____27451 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27451
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27445 uu____27449
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3610_27461 = wl  in
                     {
                       attempting = (uu___3610_27461.attempting);
                       wl_deferred = (uu___3610_27461.wl_deferred);
                       wl_deferred_to_tac =
                         (uu___3610_27461.wl_deferred_to_tac);
                       ctr = (uu___3610_27461.ctr);
                       defer_ok = (uu___3610_27461.defer_ok);
                       smt_ok = (uu___3610_27461.smt_ok);
                       umax_heuristic_ok =
                         (uu___3610_27461.umax_heuristic_ok);
                       tcenv = (uu___3610_27461.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____27462 =
                     let rec is_uvar1 t =
                       let uu____27476 =
                         let uu____27477 = FStar_Syntax_Subst.compress t  in
                         uu____27477.FStar_Syntax_Syntax.n  in
                       match uu____27476 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27481 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27496) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27502) ->
                           is_uvar1 t1
                       | uu____27527 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27561  ->
                          fun uu____27562  ->
                            fun uu____27563  ->
                              match (uu____27561, uu____27562, uu____27563)
                              with
                              | ((a1,uu____27607),(a2,uu____27609),(is_sub_probs,wl2))
                                  ->
                                  let uu____27642 = is_uvar1 a1  in
                                  if uu____27642
                                  then
                                    ((let uu____27652 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27652
                                      then
                                        let uu____27657 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27659 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27657 uu____27659
                                      else ());
                                     (let uu____27664 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27664 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27462 with
                   | (is_sub_probs,wl2) ->
                       let uu____27692 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27692 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27700 =
                              let uu____27705 =
                                let uu____27706 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27706
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27705
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27700 with
                             | (uu____27713,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27724 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27726 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27724 s uu____27726
                                    in
                                 let uu____27729 =
                                   let uu____27758 =
                                     let uu____27759 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27759.FStar_Syntax_Syntax.n  in
                                   match uu____27758 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27819 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27819 with
                                        | (a::bs1,c3) ->
                                            let uu____27875 =
                                              let uu____27894 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27894
                                                (fun uu____27998  ->
                                                   match uu____27998 with
                                                   | (l1,l2) ->
                                                       let uu____28071 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____28071))
                                               in
                                            (match uu____27875 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____28176 ->
                                       let uu____28177 =
                                         let uu____28183 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____28183)
                                          in
                                       FStar_Errors.raise_error uu____28177 r
                                    in
                                 (match uu____27729 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____28259 =
                                        let uu____28266 =
                                          let uu____28267 =
                                            let uu____28268 =
                                              let uu____28275 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____28275,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____28268
                                             in
                                          [uu____28267]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____28266
                                          (fun b  ->
                                             let uu____28291 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____28293 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28295 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____28291 uu____28293
                                               uu____28295) r
                                         in
                                      (match uu____28259 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____28305 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____28305
                                             then
                                               let uu____28310 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____28319 =
                                                          let uu____28321 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____28321
                                                           in
                                                        Prims.op_Hat s
                                                          uu____28319) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____28310
                                             else ());
                                            (let wl4 =
                                               let uu___3682_28329 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3682_28329.attempting);
                                                 wl_deferred =
                                                   (uu___3682_28329.wl_deferred);
                                                 wl_deferred_to_tac =
                                                   (uu___3682_28329.wl_deferred_to_tac);
                                                 ctr = (uu___3682_28329.ctr);
                                                 defer_ok =
                                                   (uu___3682_28329.defer_ok);
                                                 smt_ok =
                                                   (uu___3682_28329.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3682_28329.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3682_28329.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____28354 =
                                                        let uu____28361 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____28361, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____28354) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____28378 =
                                               let f_sort_is =
                                                 let uu____28388 =
                                                   let uu____28389 =
                                                     let uu____28392 =
                                                       let uu____28393 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28393.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28392
                                                      in
                                                   uu____28389.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28388 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28404,uu____28405::is)
                                                     ->
                                                     let uu____28447 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28447
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28480 ->
                                                     let uu____28481 =
                                                       let uu____28487 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28487)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28481 r
                                                  in
                                               let uu____28493 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28528  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28528
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28549 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28549
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28493
                                                in
                                             match uu____28378 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28574 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28574
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28575 =
                                                   let g_sort_is =
                                                     let uu____28585 =
                                                       let uu____28586 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28586.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28585 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28591,uu____28592::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28652 ->
                                                         let uu____28653 =
                                                           let uu____28659 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28659)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28653 r
                                                      in
                                                   let uu____28665 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28700  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28700
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28721
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28721
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28665
                                                    in
                                                 (match uu____28575 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28748 =
                                                          let uu____28753 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28754 =
                                                            let uu____28755 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28755
                                                             in
                                                          (uu____28753,
                                                            uu____28754)
                                                           in
                                                        match uu____28748
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28783 =
                                                          let uu____28786 =
                                                            let uu____28789 =
                                                              let uu____28792
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28792
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28789
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28786
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28783
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28816 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28816
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
                                                        let uu____28827 =
                                                          let uu____28830 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28833  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28833)
                                                            uu____28830
                                                           in
                                                        solve_prob orig
                                                          uu____28827 [] wl6
                                                         in
                                                      let uu____28834 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28834))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28857 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28859 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28859]
              | x -> x  in
            let c12 =
              let uu___3748_28862 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3748_28862.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3748_28862.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3748_28862.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3748_28862.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28863 =
              let uu____28868 =
                FStar_All.pipe_right
                  (let uu___3751_28870 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3751_28870.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3751_28870.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3751_28870.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3751_28870.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28868
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28863
              (fun uu____28884  ->
                 match uu____28884 with
                 | (c,g) ->
                     let uu____28891 =
                       let uu____28893 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28893  in
                     if uu____28891
                     then
                       let uu____28896 =
                         let uu____28902 =
                           let uu____28904 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28906 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28904 uu____28906
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28902)
                          in
                       FStar_Errors.raise_error uu____28896 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28912 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28912
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28918 = lift_c1 ()  in
               solve_eq uu____28918 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28927  ->
                         match uu___31_28927 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28932 -> false))
                  in
               let uu____28934 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28964)::uu____28965,(wp2,uu____28967)::uu____28968)
                     -> (wp1, wp2)
                 | uu____29041 ->
                     let uu____29066 =
                       let uu____29072 =
                         let uu____29074 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____29076 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____29074 uu____29076
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____29072)
                        in
                     FStar_Errors.raise_error uu____29066
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28934 with
               | (wpc1,wpc2) ->
                   let uu____29086 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____29086
                   then
                     let uu____29089 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29089 wl
                   else
                     (let uu____29093 =
                        let uu____29100 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____29100  in
                      match uu____29093 with
                      | (c2_decl,qualifiers) ->
                          let uu____29121 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____29121
                          then
                            let c1_repr =
                              let uu____29128 =
                                let uu____29129 =
                                  let uu____29130 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____29130  in
                                let uu____29131 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29129 uu____29131
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29128
                               in
                            let c2_repr =
                              let uu____29134 =
                                let uu____29135 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____29136 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29135 uu____29136
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29134
                               in
                            let uu____29138 =
                              let uu____29143 =
                                let uu____29145 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____29147 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____29145
                                  uu____29147
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____29143
                               in
                            (match uu____29138 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____29153 = attempt [prob] wl2  in
                                 solve env uu____29153)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____29173 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____29173
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____29196 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____29196
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
                                        let uu____29206 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____29206 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____29213 =
                                        let uu____29220 =
                                          let uu____29221 =
                                            let uu____29238 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____29241 =
                                              let uu____29252 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____29252; wpc1_2]  in
                                            (uu____29238, uu____29241)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____29221
                                           in
                                        FStar_Syntax_Syntax.mk uu____29220
                                         in
                                      uu____29213
                                        FStar_Pervasives_Native.None r))
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
                                     let uu____29301 =
                                       let uu____29308 =
                                         let uu____29309 =
                                           let uu____29326 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____29329 =
                                             let uu____29340 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____29349 =
                                               let uu____29360 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____29360; wpc1_2]  in
                                             uu____29340 :: uu____29349  in
                                           (uu____29326, uu____29329)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____29309
                                          in
                                       FStar_Syntax_Syntax.mk uu____29308  in
                                     uu____29301 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____29414 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____29414
                              then
                                let uu____29419 =
                                  let uu____29421 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____29421
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____29419
                              else ());
                             (let uu____29425 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____29425 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____29434 =
                                      let uu____29437 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _29440  ->
                                           FStar_Pervasives_Native.Some
                                             _29440) uu____29437
                                       in
                                    solve_prob orig uu____29434 [] wl1  in
                                  let uu____29441 = attempt [base_prob] wl2
                                     in
                                  solve env uu____29441))))
           in
        let uu____29442 = FStar_Util.physical_equality c1 c2  in
        if uu____29442
        then
          let uu____29445 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29445
        else
          ((let uu____29449 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29449
            then
              let uu____29454 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29456 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29454
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29456
            else ());
           (let uu____29461 =
              let uu____29470 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29473 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29470, uu____29473)  in
            match uu____29461 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29491),FStar_Syntax_Syntax.Total
                    (t2,uu____29493)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29510 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29510 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29512,FStar_Syntax_Syntax.Total uu____29513) ->
                     let uu____29530 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29530 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29534),FStar_Syntax_Syntax.Total
                    (t2,uu____29536)) ->
                     let uu____29553 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29553 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29556),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29558)) ->
                     let uu____29575 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29575 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29578),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29580)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29597 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29597 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29600),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29602)) ->
                     let uu____29619 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29619 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29622,FStar_Syntax_Syntax.Comp uu____29623) ->
                     let uu____29632 =
                       let uu___3875_29635 = problem  in
                       let uu____29638 =
                         let uu____29639 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29639
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3875_29635.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29638;
                         FStar_TypeChecker_Common.relation =
                           (uu___3875_29635.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3875_29635.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3875_29635.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3875_29635.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3875_29635.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3875_29635.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3875_29635.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3875_29635.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29632 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29640,FStar_Syntax_Syntax.Comp uu____29641) ->
                     let uu____29650 =
                       let uu___3875_29653 = problem  in
                       let uu____29656 =
                         let uu____29657 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29657
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3875_29653.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29656;
                         FStar_TypeChecker_Common.relation =
                           (uu___3875_29653.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3875_29653.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3875_29653.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3875_29653.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3875_29653.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3875_29653.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3875_29653.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3875_29653.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29650 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29658,FStar_Syntax_Syntax.GTotal uu____29659) ->
                     let uu____29668 =
                       let uu___3887_29671 = problem  in
                       let uu____29674 =
                         let uu____29675 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29675
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3887_29671.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3887_29671.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3887_29671.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29674;
                         FStar_TypeChecker_Common.element =
                           (uu___3887_29671.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3887_29671.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3887_29671.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3887_29671.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3887_29671.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3887_29671.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29668 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29676,FStar_Syntax_Syntax.Total uu____29677) ->
                     let uu____29686 =
                       let uu___3887_29689 = problem  in
                       let uu____29692 =
                         let uu____29693 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29693
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3887_29689.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3887_29689.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3887_29689.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29692;
                         FStar_TypeChecker_Common.element =
                           (uu___3887_29689.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3887_29689.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3887_29689.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3887_29689.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3887_29689.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3887_29689.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29686 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29694,FStar_Syntax_Syntax.Comp uu____29695) ->
                     let uu____29696 =
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
                     if uu____29696
                     then
                       let uu____29699 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29699 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29706 =
                            let uu____29711 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29711
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29720 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29721 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29720, uu____29721))
                             in
                          match uu____29706 with
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
                           (let uu____29729 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29729
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29737 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29737 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29740 =
                                  FStar_Thunk.mk
                                    (fun uu____29745  ->
                                       let uu____29746 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29748 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29746 uu____29748)
                                   in
                                giveup env uu____29740 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29759 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29759 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29809 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29809 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29834 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29865  ->
                match uu____29865 with
                | (u1,u2) ->
                    let uu____29873 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29875 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29873 uu____29875))
         in
      FStar_All.pipe_right uu____29834 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29912,[])) when
          let uu____29939 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29939 -> "{}"
      | uu____29942 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29969 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29969
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry defs =
            let uu____30000 =
              FStar_List.map
                (fun uu____30014  ->
                   match uu____30014 with
                   | (msg,x) ->
                       let uu____30025 =
                         let uu____30027 = prob_to_string env x  in
                         Prims.op_Hat ": " uu____30027  in
                       Prims.op_Hat msg uu____30025) defs
               in
            FStar_All.pipe_right uu____30000 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30037 = carry g.FStar_TypeChecker_Common.deferred  in
          let uu____30039 = carry g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____30041 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30037 uu____30039 uu____30041 imps
  
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
                  let uu____30098 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30098
                  then
                    let uu____30106 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30108 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30106
                      (rel_to_string rel) uu____30108
                  else "TOP"  in
                let uu____30114 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30114 with
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
              let uu____30174 =
                let uu____30177 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _30180  -> FStar_Pervasives_Native.Some _30180)
                  uu____30177
                 in
              FStar_Syntax_Syntax.new_bv uu____30174 t1  in
            let uu____30181 =
              let uu____30186 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30186
               in
            match uu____30181 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____30258 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30258
         then
           let uu____30263 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30263
         else ());
        (let uu____30270 =
           FStar_Util.record_time (fun uu____30277  -> solve env probs)  in
         match uu____30270 with
         | (sol,ms) ->
             ((let uu____30291 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30291
               then
                 let uu____30296 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30296
               else ());
              (match sol with
               | Success (deferred,defer_to_tac,implicits) ->
                   let uu____30312 =
                     FStar_Util.record_time
                       (fun uu____30319  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30312 with
                    | ((),ms1) ->
                        ((let uu____30332 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30332
                          then
                            let uu____30337 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30337
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d,s) ->
                   ((let uu____30351 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30351
                     then
                       let uu____30358 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30358
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
          ((let uu____30386 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30386
            then
              let uu____30391 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30391
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30399 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30399
             then
               let uu____30404 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30404
             else ());
            (let f2 =
               let uu____30410 =
                 let uu____30411 = FStar_Syntax_Util.unmeta f1  in
                 uu____30411.FStar_Syntax_Syntax.n  in
               match uu____30410 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30415 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4006_30416 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4006_30416.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4006_30416.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4006_30416.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4006_30416.FStar_TypeChecker_Common.implicits)
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
            let uu____30468 =
              let uu____30469 =
                let uu____30470 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _30471  ->
                       FStar_TypeChecker_Common.NonTrivial _30471)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30470;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30469  in
            FStar_All.pipe_left
              (fun _30478  -> FStar_Pervasives_Native.Some _30478)
              uu____30468
  
let with_guard_no_simp :
  'Auu____30488 .
    'Auu____30488 ->
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
            let uu____30537 =
              let uu____30538 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _30539  -> FStar_TypeChecker_Common.NonTrivial _30539)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30538;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30537
  
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
          (let uu____30572 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30572
           then
             let uu____30577 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30579 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30577
               uu____30579
           else ());
          (let uu____30584 =
             let uu____30589 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30589
              in
           match uu____30584 with
           | (prob,wl) ->
               let g =
                 let uu____30597 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30607  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30597  in
               ((let uu____30629 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30629
                 then
                   let uu____30634 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30634
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
        let uu____30655 = try_teq true env t1 t2  in
        match uu____30655 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30660 = FStar_TypeChecker_Env.get_range env  in
              let uu____30661 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30660 uu____30661);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30669 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30669
              then
                let uu____30674 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30676 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30678 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30674
                  uu____30676 uu____30678
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
        (let uu____30702 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30702
         then
           let uu____30707 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30709 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30707
             uu____30709
         else ());
        (let uu____30714 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30714 with
         | (prob,x,wl) ->
             let g =
               let uu____30729 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30740  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30729  in
             ((let uu____30762 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30762
               then
                 let uu____30767 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30767
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30775 =
                     let uu____30776 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30776 g1  in
                   FStar_Pervasives_Native.Some uu____30775)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30798 = FStar_TypeChecker_Env.get_range env  in
          let uu____30799 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30798 uu____30799
  
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
        (let uu____30828 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30828
         then
           let uu____30833 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30835 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30833 uu____30835
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30846 =
           let uu____30853 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30853 "sub_comp"
            in
         match uu____30846 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30866 =
                 FStar_Util.record_time
                   (fun uu____30878  ->
                      let uu____30879 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30890  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30879)
                  in
               match uu____30866 with
               | (r,ms) ->
                   ((let uu____30922 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30922
                     then
                       let uu____30927 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30929 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30931 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30927 uu____30929
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30931
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
      fun uu____30969  ->
        match uu____30969 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31012 =
                 let uu____31018 =
                   let uu____31020 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31022 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31020 uu____31022
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31018)  in
               let uu____31026 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31012 uu____31026)
               in
            let equiv1 v1 v' =
              let uu____31039 =
                let uu____31044 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____31045 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31044, uu____31045)  in
              match uu____31039 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31065 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____31096 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____31096 with
                      | FStar_Syntax_Syntax.U_unif uu____31103 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31132  ->
                                    match uu____31132 with
                                    | (u,v') ->
                                        let uu____31141 = equiv1 v1 v'  in
                                        if uu____31141
                                        then
                                          let uu____31146 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____31146 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____31167 -> []))
               in
            let uu____31172 =
              let wl =
                let uu___4119_31176 = empty_worklist env  in
                {
                  attempting = (uu___4119_31176.attempting);
                  wl_deferred = (uu___4119_31176.wl_deferred);
                  wl_deferred_to_tac = (uu___4119_31176.wl_deferred_to_tac);
                  ctr = (uu___4119_31176.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4119_31176.smt_ok);
                  umax_heuristic_ok = (uu___4119_31176.umax_heuristic_ok);
                  tcenv = (uu___4119_31176.tcenv);
                  wl_implicits = (uu___4119_31176.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31195  ->
                      match uu____31195 with
                      | (lb,v1) ->
                          let uu____31202 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____31202 with
                           | USolved wl1 -> ()
                           | uu____31205 -> fail1 lb v1)))
               in
            let rec check_ineq uu____31216 =
              match uu____31216 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31228) -> true
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
                      uu____31252,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31254,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31265) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____31273,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____31282 -> false)
               in
            let uu____31288 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31305  ->
                      match uu____31305 with
                      | (u,v1) ->
                          let uu____31313 = check_ineq (u, v1)  in
                          if uu____31313
                          then true
                          else
                            ((let uu____31321 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31321
                              then
                                let uu____31326 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31328 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____31326
                                  uu____31328
                              else ());
                             false)))
               in
            if uu____31288
            then ()
            else
              ((let uu____31338 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31338
                then
                  ((let uu____31344 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31344);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31356 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31356))
                else ());
               (let uu____31369 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31369))
  
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
    FStar_TypeChecker_Env.env ->
      FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun defer_ok  ->
    fun env  ->
      fun g  ->
        let fail1 uu____31444 =
          match uu____31444 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4196_31471 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4196_31471.attempting);
            wl_deferred = (uu___4196_31471.wl_deferred);
            wl_deferred_to_tac = (uu___4196_31471.wl_deferred_to_tac);
            ctr = (uu___4196_31471.ctr);
            defer_ok;
            smt_ok = (uu___4196_31471.smt_ok);
            umax_heuristic_ok = (uu___4196_31471.umax_heuristic_ok);
            tcenv = (uu___4196_31471.tcenv);
            wl_implicits = (uu___4196_31471.wl_implicits)
          }  in
        (let uu____31474 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31474
         then
           let uu____31479 = FStar_Util.string_of_bool defer_ok  in
           let uu____31481 = wl_to_string wl  in
           let uu____31483 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____31479 uu____31481 uu____31483
         else ());
        (let g1 =
           let uu____31489 = solve_and_commit env wl fail1  in
           match uu____31489 with
           | FStar_Pervasives_Native.Some
               (uu____31498::uu____31499,uu____31500,uu____31501) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,defer_to_tac,imps) ->
               let uu___4213_31535 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4213_31535.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred_to_tac =
                   (FStar_List.append
                      g.FStar_TypeChecker_Common.deferred_to_tac defer_to_tac);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4213_31535.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____31541 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4218_31552 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4218_31552.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4218_31552.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4218_31552.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4218_31552.FStar_TypeChecker_Common.implicits)
          }))
  
let (solve_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints false env g 
let (solve_some_deferred_constraints :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> try_solve_deferred_constraints true env g 
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
          let debug1 =
            ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel"))
               ||
               (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "SMTQuery")))
              ||
              (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Tac"))
             in
          (let uu____31628 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____31628
           then
             let uu____31633 = guard_to_string env g  in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31633
           else ());
          (let g1 = solve_deferred_constraints env g  in
           let ret_g =
             let uu___4232_31640 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4232_31640.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4232_31640.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4232_31640.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4232_31640.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31641 =
             let uu____31643 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31643  in
           if uu____31641
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug1
                   then
                     (let uu____31655 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31656 =
                        let uu____31658 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31658
                         in
                      FStar_Errors.diag uu____31655 uu____31656)
                   else ();
                   (let vc1 =
                      let uu____31664 =
                        let uu____31668 =
                          let uu____31670 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31670  in
                        FStar_Pervasives_Native.Some uu____31668  in
                      FStar_Profiling.profile
                        (fun uu____31673  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31664 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug1
                    then
                      (let uu____31677 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31678 =
                         let uu____31680 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31680
                          in
                       FStar_Errors.diag uu____31677 uu____31678)
                    else ();
                    (let uu____31686 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31686 "discharge_guard'" env vc1);
                    (let uu____31688 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31688 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug1
                            then
                              (let uu____31697 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31698 =
                                 let uu____31700 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31700
                                  in
                               FStar_Errors.diag uu____31697 uu____31698)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug1
                            then
                              (let uu____31710 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31711 =
                                 let uu____31713 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31713
                                  in
                               FStar_Errors.diag uu____31710 uu____31711)
                            else ();
                            (let vcs =
                               let uu____31727 = FStar_Options.use_tactics ()
                                  in
                               if uu____31727
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31749  ->
                                      (let uu____31751 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left (fun a1  -> ())
                                         uu____31751);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31795  ->
                                               match uu____31795 with
                                               | (env1,goal,opts) ->
                                                   let uu____31811 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____31811, opts)))))
                               else
                                 (let uu____31815 =
                                    let uu____31822 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____31822)  in
                                  [uu____31815])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____31855  ->
                                     match uu____31855 with
                                     | (env1,goal,opts) ->
                                         let uu____31865 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____31865 with
                                          | FStar_TypeChecker_Common.Trivial 
                                              ->
                                              if debug1
                                              then
                                                FStar_Util.print_string
                                                  "Goal completely solved by tactic\n"
                                              else ()
                                          | FStar_TypeChecker_Common.NonTrivial
                                              goal1 ->
                                              (FStar_Options.push ();
                                               FStar_Options.set opts;
                                               if debug1
                                               then
                                                 (let uu____31876 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31877 =
                                                    let uu____31879 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____31881 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____31879 uu____31881
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31876 uu____31877)
                                               else ();
                                               if debug1
                                               then
                                                 (let uu____31888 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31889 =
                                                    let uu____31891 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____31891
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31888 uu____31889)
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
      let uu____31909 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31909 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31918 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31918
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31932 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31932 with
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
        let uu____31962 = try_teq false env t1 t2  in
        match uu____31962 with
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
            let uu____32006 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32006 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32013 ->
                     let uu____32014 =
                       let uu____32015 = FStar_Syntax_Subst.compress r  in
                       uu____32015.FStar_Syntax_Syntax.n  in
                     (match uu____32014 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32020) ->
                          unresolved ctx_u'
                      | uu____32037 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32061 = acc  in
            match uu____32061 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____32080 = hd1  in
                     (match uu____32080 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____32091 = unresolved ctx_u  in
                             if uu____32091
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32102 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32102
                                     then
                                       let uu____32106 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32106
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32115 = teq_nosmt env1 t tm
                                          in
                                       match uu____32115 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4345_32125 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4345_32125.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4345_32125.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4345_32125.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4345_32125.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4345_32125.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4345_32125.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4345_32125.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4348_32127 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4348_32127.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4348_32127.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4348_32127.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                               | uu____32130 ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4353_32142 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4353_32142.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4353_32142.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4353_32142.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4353_32142.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4353_32142.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4353_32142.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4353_32142.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4353_32142.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4353_32142.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4353_32142.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4353_32142.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4353_32142.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4353_32142.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4353_32142.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4353_32142.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4353_32142.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4353_32142.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4353_32142.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4353_32142.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4353_32142.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4353_32142.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4353_32142.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4353_32142.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4353_32142.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4353_32142.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4353_32142.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4353_32142.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4353_32142.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4353_32142.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4353_32142.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4353_32142.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4353_32142.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4353_32142.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4353_32142.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4353_32142.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4353_32142.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4353_32142.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4353_32142.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4353_32142.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4353_32142.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4353_32142.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4353_32142.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4353_32142.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4353_32142.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4353_32142.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4353_32142.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___4353_32142.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4358_32147 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4358_32147.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4358_32147.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4358_32147.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4358_32147.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4358_32147.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4358_32147.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4358_32147.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4358_32147.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4358_32147.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4358_32147.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4358_32147.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4358_32147.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4358_32147.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4358_32147.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4358_32147.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4358_32147.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4358_32147.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4358_32147.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4358_32147.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4358_32147.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4358_32147.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4358_32147.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4358_32147.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4358_32147.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4358_32147.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4358_32147.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4358_32147.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4358_32147.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4358_32147.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4358_32147.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4358_32147.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4358_32147.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4358_32147.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4358_32147.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4358_32147.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4358_32147.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4358_32147.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      }
                                    else env1  in
                                  (let uu____32152 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32152
                                   then
                                     let uu____32157 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32159 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32161 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32163 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32157 uu____32159 uu____32161
                                       reason uu____32163
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4364_32170  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32177 =
                                             let uu____32187 =
                                               let uu____32195 =
                                                 let uu____32197 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32199 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32201 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32197 uu____32199
                                                   uu____32201
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32195, r)
                                                in
                                             [uu____32187]  in
                                           FStar_Errors.add_errors
                                             uu____32177);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32220 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32231  ->
                                               let uu____32232 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32234 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32236 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32232 uu____32234
                                                 reason uu____32236)) env2 g1
                                         true
                                        in
                                     match uu____32220 with
                                     | FStar_Pervasives_Native.Some g2 -> g2
                                     | FStar_Pervasives_Native.None  ->
                                         failwith
                                           "Impossible, with use_smt = true, discharge_guard' should never have returned None"
                                      in
                                   until_fixpoint
                                     ((FStar_List.append
                                         g'.FStar_TypeChecker_Common.implicits
                                         out), true) tl1)))))
             in
          let uu___4376_32244 = g  in
          let uu____32245 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4376_32244.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4376_32244.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4376_32244.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4376_32244.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32245
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____32260 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32260
       then
         let uu____32265 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32265
       else ());
      resolve_implicits' env
        ((Prims.op_Negation env.FStar_TypeChecker_Env.phase1) &&
           (Prims.op_Negation env.FStar_TypeChecker_Env.lax)) false g
  
let (resolve_implicits_tac :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  = fun env  -> fun g  -> resolve_implicits' env false true g 
type goal_type =
  | FlexRigid of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term) 
  | FlexFlex of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.ctx_uvar)
  
  | Frame of (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term) 
  | Imp of FStar_Syntax_Syntax.ctx_uvar 
let (uu___is_FlexRigid : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | FlexRigid _0 -> true | uu____32332 -> false
  
let (__proj__FlexRigid__item___0 :
  goal_type -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | FlexRigid _0 -> _0 
let (uu___is_FlexFlex : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | FlexFlex _0 -> true | uu____32367 -> false
  
let (__proj__FlexFlex__item___0 :
  goal_type -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.ctx_uvar))
  = fun projectee  -> match projectee with | FlexFlex _0 -> _0 
let (uu___is_Frame : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Frame _0 -> true | uu____32404 -> false
  
let (__proj__Frame__item___0 :
  goal_type ->
    (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | Frame _0 -> _0 
let (uu___is_Imp : goal_type -> Prims.bool) =
  fun projectee  ->
    match projectee with | Imp _0 -> true | uu____32441 -> false
  
let (__proj__Imp__item___0 : goal_type -> FStar_Syntax_Syntax.ctx_uvar) =
  fun projectee  -> match projectee with | Imp _0 -> _0 
type goal_dep =
  {
  goal_dep_id: Prims.int ;
  goal_type: goal_type ;
  goal_imp: FStar_TypeChecker_Common.implicit ;
  assignees: FStar_Syntax_Syntax.ctx_uvar FStar_Util.set ;
  dependences: goal_dep Prims.list ;
  visited: Prims.int FStar_ST.ref }
let (__proj__Mkgoal_dep__item__goal_dep_id : goal_dep -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; dependences; visited;_}
        -> goal_dep_id
  
let (__proj__Mkgoal_dep__item__goal_type : goal_dep -> goal_type) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; dependences; visited;_}
        -> goal_type
  
let (__proj__Mkgoal_dep__item__goal_imp :
  goal_dep -> FStar_TypeChecker_Common.implicit) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; dependences; visited;_}
        -> goal_imp
  
let (__proj__Mkgoal_dep__item__assignees :
  goal_dep -> FStar_Syntax_Syntax.ctx_uvar FStar_Util.set) =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; dependences; visited;_}
        -> assignees
  
let (__proj__Mkgoal_dep__item__dependences : goal_dep -> goal_dep Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; dependences; visited;_}
        -> dependences
  
let (__proj__Mkgoal_dep__item__visited : goal_dep -> Prims.int FStar_ST.ref)
  =
  fun projectee  ->
    match projectee with
    | { goal_dep_id; goal_type; goal_imp; assignees; dependences; visited;_}
        -> visited
  
let (print_goal_dep : goal_dep -> unit) =
  fun gd  ->
    let uu____32666 = FStar_Util.string_of_int gd.goal_dep_id  in
    let uu____32668 =
      let uu____32670 =
        let uu____32674 = FStar_Util.set_elements gd.assignees  in
        FStar_All.pipe_right uu____32674
          (FStar_List.map
             (fun u  ->
                let uu____32686 =
                  let uu____32688 =
                    FStar_Syntax_Unionfind.uvar_id
                      u.FStar_Syntax_Syntax.ctx_uvar_head
                     in
                  FStar_All.pipe_left FStar_Util.string_of_int uu____32688
                   in
                Prims.op_Hat "?" uu____32686))
         in
      FStar_All.pipe_right uu____32670 (FStar_String.concat "; ")  in
    let uu____32698 =
      let uu____32700 =
        FStar_List.map (fun gd1  -> FStar_Util.string_of_int gd1.goal_dep_id)
          gd.dependences
         in
      FStar_All.pipe_right uu____32700 (FStar_String.concat "; ")  in
    let uu____32712 =
      FStar_Syntax_Print.ctx_uvar_to_string
        (gd.goal_imp).FStar_TypeChecker_Common.imp_uvar
       in
    FStar_Util.print4 "%s:{assignees=[%s], dependences=[%s]}\n\t%s\n"
      uu____32666 uu____32668 uu____32698 uu____32712
  
let (sort_goals :
  FStar_TypeChecker_Common.implicits ->
    FStar_TypeChecker_Common.implicits -> FStar_TypeChecker_Common.implicits)
  =
  fun eqs  ->
    fun rest  ->
      let goal_dep_id = FStar_Util.mk_ref Prims.int_zero  in
      let uu____32732 = (Prims.int_zero, Prims.int_one, (Prims.of_int (2)))
         in
      match uu____32732 with
      | (mark_unset,mark_temp,mark_set) ->
          let empty_uv_set = FStar_Syntax_Free.new_uv_set ()  in
          let eq_as_goal_dep eq1 =
            let uu____32764 =
              match ((eq1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ).FStar_Syntax_Syntax.n
              with
              | FStar_Syntax_Syntax.Tm_app
                  ({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uinst
                       ({
                          FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                            fv;
                          FStar_Syntax_Syntax.pos = uu____32778;
                          FStar_Syntax_Syntax.vars = uu____32779;_},uu____32780);
                     FStar_Syntax_Syntax.pos = uu____32781;
                     FStar_Syntax_Syntax.vars = uu____32782;_},uu____32783::
                   (lhs,uu____32785)::(rhs,uu____32787)::[])
                  when
                  FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eq2_lid
                  ->
                  let flex_lhs = is_flex lhs  in
                  let flex_rhs = is_flex rhs  in
                  if flex_lhs && flex_rhs
                  then
                    let uu____32873 =
                      let uu____32878 = flex_uvar_head lhs  in
                      let uu____32879 = flex_uvar_head rhs  in
                      (uu____32878, uu____32879)  in
                    (match uu____32873 with
                     | (lhs1,rhs1) ->
                         let uu____32888 =
                           let uu____32891 =
                             FStar_Util.set_add lhs1 empty_uv_set  in
                           FStar_Util.set_add rhs1 uu____32891  in
                         ((FlexFlex (lhs1, rhs1)), uu____32888))
                  else
                    if flex_lhs
                    then
                      (let lhs1 = flex_uvar_head lhs  in
                       let uu____32906 = FStar_Util.set_add lhs1 empty_uv_set
                          in
                       ((FlexRigid (lhs1, rhs)), uu____32906))
                    else
                      if flex_rhs
                      then
                        (let rhs1 = flex_uvar_head rhs  in
                         let uu____32921 =
                           FStar_Util.set_add rhs1 empty_uv_set  in
                         ((FlexRigid (rhs1, lhs)), uu____32921))
                      else
                        failwith
                          "Impossible: deferred goals must be flex on one at least one side"
              | uu____32935 -> failwith "Not an eq"  in
            match uu____32764 with
            | (goal_type,assignees) ->
                (FStar_Util.incr goal_dep_id;
                 (let uu____32950 = FStar_ST.op_Bang goal_dep_id  in
                  let uu____32973 = FStar_Util.mk_ref mark_unset  in
                  {
                    goal_dep_id = uu____32950;
                    goal_type;
                    goal_imp = eq1;
                    assignees;
                    dependences = [];
                    visited = uu____32973
                  }))
             in
          let imp_as_goal_dep i =
            FStar_Util.incr goal_dep_id;
            (let uu____32985 =
               FStar_Syntax_Util.head_and_args
                 (i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                in
             match uu____32985 with
             | (head1,args) ->
                 let uu____33028 =
                   let uu____33043 =
                     let uu____33044 = FStar_Syntax_Util.un_uinst head1  in
                     uu____33044.FStar_Syntax_Syntax.n  in
                   (uu____33043, args)  in
                 (match uu____33028 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     fv,(outer,uu____33059)::(inner,uu____33061)::[]) when
                      let uu____33112 =
                        FStar_Ident.lid_of_str "Repro.split_frame"  in
                      FStar_Syntax_Syntax.fv_eq_lid fv uu____33112 ->
                      let uu____33114 = FStar_ST.op_Bang goal_dep_id  in
                      let uu____33137 =
                        FStar_Util.set_add
                          i.FStar_TypeChecker_Common.imp_uvar empty_uv_set
                         in
                      let uu____33140 = FStar_Util.mk_ref mark_unset  in
                      {
                        goal_dep_id = uu____33114;
                        goal_type =
                          (Frame
                             ((i.FStar_TypeChecker_Common.imp_uvar), outer,
                               inner));
                        goal_imp = i;
                        assignees = uu____33137;
                        dependences = [];
                        visited = uu____33140
                      }
                  | uu____33145 ->
                      ((let uu____33161 =
                          FStar_Syntax_Print.term_to_string head1  in
                        let uu____33163 =
                          FStar_Syntax_Print.args_to_string args  in
                        FStar_Util.print2
                          "Discarding goal as imp: head=%s, args=%s\n"
                          uu____33161 uu____33163);
                       (let uu____33166 = FStar_ST.op_Bang goal_dep_id  in
                        let uu____33189 = FStar_Util.mk_ref mark_unset  in
                        {
                          goal_dep_id = uu____33166;
                          goal_type =
                            (Imp (i.FStar_TypeChecker_Common.imp_uvar));
                          goal_imp = i;
                          assignees = empty_uv_set;
                          dependences = [];
                          visited = uu____33189
                        }))))
             in
          let goal_deps =
            let uu____33197 = FStar_List.map eq_as_goal_dep eqs  in
            let uu____33200 = FStar_List.map imp_as_goal_dep rest  in
            FStar_List.append uu____33197 uu____33200  in
          let uu____33203 =
            FStar_List.partition
              (fun gd  ->
                 match gd.goal_type with
                 | Imp uu____33216 -> false
                 | uu____33218 -> true) goal_deps
             in
          (match uu____33203 with
           | (goal_deps1,rest1) ->
               let fill_deps_of_goal gd =
                 let dependent_uvars =
                   match gd.goal_type with
                   | FlexRigid (flex,t) -> FStar_Syntax_Free.uvars t
                   | FlexFlex (lhs,rhs) -> gd.assignees
                   | Frame (uu____33245,outer,inner) ->
                       let uu____33248 = FStar_Syntax_Free.uvars outer  in
                       let uu____33251 = FStar_Syntax_Free.uvars inner  in
                       FStar_Util.set_union uu____33248 uu____33251
                   | Imp uu____33254 ->
                       failwith "Impossible: should be filtered out"
                    in
                 let deps =
                   FStar_List.filter
                     (fun other_gd  ->
                        let uu____33264 =
                          FStar_Util.physical_equality gd other_gd  in
                        if uu____33264
                        then false
                        else
                          (let uu____33271 =
                             let uu____33273 =
                               FStar_Util.set_intersect dependent_uvars
                                 other_gd.assignees
                                in
                             FStar_Util.set_is_empty uu____33273  in
                           Prims.op_Negation uu____33271)) goal_deps1
                    in
                 let uu___4502_33276 = gd  in
                 {
                   goal_dep_id = (uu___4502_33276.goal_dep_id);
                   goal_type = (uu___4502_33276.goal_type);
                   goal_imp = (uu___4502_33276.goal_imp);
                   assignees = (uu___4502_33276.assignees);
                   dependences = deps;
                   visited = (uu___4502_33276.visited)
                 }  in
               let topological_sort gds =
                 let out = FStar_Util.mk_ref []  in
                 let rec visit gd =
                   let uu____33302 =
                     let uu____33304 = FStar_ST.op_Bang gd.visited  in
                     uu____33304 = mark_set  in
                   if uu____33302
                   then ()
                   else
                     (let uu____33331 =
                        let uu____33333 = FStar_ST.op_Bang gd.visited  in
                        uu____33333 = mark_temp  in
                      if uu____33331
                      then failwith "Cycle"
                      else
                        (FStar_ST.op_Colon_Equals gd.visited mark_temp;
                         FStar_List.iter visit gd.dependences;
                         FStar_ST.op_Colon_Equals gd.visited mark_set;
                         (let uu____33406 =
                            let uu____33409 = FStar_ST.op_Bang out  in gd ::
                              uu____33409
                             in
                          FStar_ST.op_Colon_Equals out uu____33406)))
                    in
                 FStar_List.iter visit gds; FStar_ST.op_Bang out  in
               let goal_deps2 = FStar_List.map fill_deps_of_goal goal_deps1
                  in
               (FStar_Util.print_string
                  "<<<<<<<<<<<<Goals before sorting>>>>>>>>>>>>>>>\n";
                FStar_List.iter print_goal_dep goal_deps2;
                (let goal_deps3 =
                   let uu____33491 = topological_sort goal_deps2  in
                   FStar_List.rev uu____33491  in
                 FStar_Util.print_string
                   "<<<<<<<<<<<<Goals after sorting>>>>>>>>>>>>>>>\n";
                 FStar_List.iter print_goal_dep goal_deps3;
                 FStar_List.map (fun gd  -> gd.goal_imp)
                   (FStar_List.append goal_deps3 rest1))))
  
let (force_trivial_guard :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.guard_t -> unit) =
  fun env  ->
    fun g  ->
      (let uu____33511 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____33511
       then
         let uu____33516 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____33516
       else ());
      (let solve_deferred_to_tactic g1 =
         let deferred = g1.FStar_TypeChecker_Common.deferred_to_tac  in
         match deferred with
         | [] -> g1
         | uu____33533 ->
             let prob_as_implicit uu____33544 =
               match uu____33544 with
               | (reason,prob) ->
                   (match prob with
                    | FStar_TypeChecker_Common.TProb tp when
                        tp.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ
                        ->
                        let env1 =
                          let uu___4537_33558 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4537_33558.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4537_33558.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4537_33558.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              ((tp.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4537_33558.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4537_33558.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4537_33558.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4537_33558.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4537_33558.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4537_33558.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4537_33558.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4537_33558.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4537_33558.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4537_33558.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4537_33558.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4537_33558.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4537_33558.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4537_33558.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4537_33558.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4537_33558.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___4537_33558.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4537_33558.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4537_33558.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4537_33558.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4537_33558.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4537_33558.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4537_33558.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4537_33558.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4537_33558.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4537_33558.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___4537_33558.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4537_33558.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4537_33558.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4537_33558.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4537_33558.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4537_33558.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4537_33558.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4537_33558.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4537_33558.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4537_33558.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___4537_33558.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4537_33558.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4537_33558.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4537_33558.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4537_33558.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4537_33558.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4537_33558.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4537_33558.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let env_lax =
                          let uu___4540_33560 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4540_33560.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4540_33560.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4540_33560.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___4540_33560.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4540_33560.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4540_33560.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4540_33560.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4540_33560.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4540_33560.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4540_33560.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4540_33560.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4540_33560.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4540_33560.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4540_33560.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4540_33560.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4540_33560.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4540_33560.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4540_33560.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4540_33560.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4540_33560.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4540_33560.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4540_33560.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4540_33560.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4540_33560.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4540_33560.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4540_33560.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4540_33560.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4540_33560.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4540_33560.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts = true;
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4540_33560.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4540_33560.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4540_33560.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4540_33560.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4540_33560.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4540_33560.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4540_33560.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4540_33560.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4540_33560.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___4540_33560.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4540_33560.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4540_33560.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4540_33560.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4540_33560.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4540_33560.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4540_33560.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4540_33560.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let uu____33563 =
                          env1.FStar_TypeChecker_Env.type_of env_lax
                            tp.FStar_TypeChecker_Common.lhs
                           in
                        (match uu____33563 with
                         | (uu____33570,tlhs,uu____33572) ->
                             let goal_ty =
                               let uu____33574 =
                                 env1.FStar_TypeChecker_Env.universe_of
                                   env_lax tlhs
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____33574 tlhs
                                 tp.FStar_TypeChecker_Common.lhs
                                 tp.FStar_TypeChecker_Common.rhs
                                in
                             let uu____33575 =
                               FStar_TypeChecker_Env.new_implicit_var_aux
                                 reason
                                 (tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos
                                 env1 goal_ty
                                 FStar_Syntax_Syntax.Allow_untyped
                                 FStar_Pervasives_Native.None
                                in
                             (match uu____33575 with
                              | (goal,ctx_uvar,uu____33590) ->
                                  let uu____33603 =
                                    let uu____33604 = FStar_List.hd ctx_uvar
                                       in
                                    FStar_Pervasives_Native.fst uu____33604
                                     in
                                  {
                                    FStar_TypeChecker_Common.imp_reason = "";
                                    FStar_TypeChecker_Common.imp_uvar =
                                      uu____33603;
                                    FStar_TypeChecker_Common.imp_tm = goal;
                                    FStar_TypeChecker_Common.imp_range =
                                      ((tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos)
                                  }))
                    | uu____33614 ->
                        failwith "Unexpected problem deferred to tactic")
                in
             let deferred_goals =
               FStar_List.map prob_as_implicit
                 g1.FStar_TypeChecker_Common.deferred_to_tac
                in
             let uu____33624 =
               FStar_List.partition
                 (fun imp  ->
                    let uu____33636 =
                      FStar_Syntax_Unionfind.find
                        (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                       in
                    match uu____33636 with
                    | FStar_Pervasives_Native.None  -> true
                    | uu____33641 -> false)
                 g1.FStar_TypeChecker_Common.implicits
                in
             (match uu____33624 with
              | (more,imps) ->
                  let more1 =
                    FStar_All.pipe_right more
                      (FStar_List.map
                         (fun i  ->
                            match (i.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_meta
                            with
                            | FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Ctx_uvar_meta_attr a) ->
                                let reason =
                                  let uu____33668 =
                                    FStar_Syntax_Print.term_to_string a  in
                                  FStar_Util.format2 "%s::%s" uu____33668
                                    i.FStar_TypeChecker_Common.imp_reason
                                   in
                                let uu___4565_33671 = i  in
                                {
                                  FStar_TypeChecker_Common.imp_reason =
                                    reason;
                                  FStar_TypeChecker_Common.imp_uvar =
                                    (uu___4565_33671.FStar_TypeChecker_Common.imp_uvar);
                                  FStar_TypeChecker_Common.imp_tm =
                                    (uu___4565_33671.FStar_TypeChecker_Common.imp_tm);
                                  FStar_TypeChecker_Common.imp_range =
                                    (uu___4565_33671.FStar_TypeChecker_Common.imp_range)
                                }
                            | uu____33672 -> i))
                     in
                  let deferred_goals1 = sort_goals deferred_goals more1  in
                  let guard =
                    let uu___4570_33677 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___4570_33677.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac = [];
                      FStar_TypeChecker_Common.deferred =
                        (uu___4570_33677.FStar_TypeChecker_Common.deferred);
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___4570_33677.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits = imps
                    }  in
                  let resolve_tac =
                    let uu____33684 =
                      FStar_TypeChecker_Env.lookup_attr env
                        FStar_Parser_Const.resolve_implicits_attr_string
                       in
                    match uu____33684 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let (uu____33687,lid::[]);
                        FStar_Syntax_Syntax.sigrng = uu____33689;
                        FStar_Syntax_Syntax.sigquals = uu____33690;
                        FStar_Syntax_Syntax.sigmeta = uu____33691;
                        FStar_Syntax_Syntax.sigattrs = uu____33692;
                        FStar_Syntax_Syntax.sigopts = uu____33693;_}::uu____33694
                        ->
                        let qn = FStar_TypeChecker_Env.lookup_qname env lid
                           in
                        let fv =
                          FStar_Syntax_Syntax.lid_as_fv lid
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_zero) FStar_Pervasives_Native.None
                           in
                        let dd =
                          let uu____33709 =
                            FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn
                             in
                          match uu____33709 with
                          | FStar_Pervasives_Native.Some dd -> dd
                          | FStar_Pervasives_Native.None  ->
                              failwith "Expected a dd"
                           in
                        let term =
                          let uu____33715 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Syntax_Syntax.fv_to_tm uu____33715  in
                        term
                    | uu____33716 -> failwith "Resolve_tac not found"  in
                  let env1 =
                    let uu___4595_33721 = env  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___4595_33721.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___4595_33721.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___4595_33721.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___4595_33721.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___4595_33721.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___4595_33721.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___4595_33721.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___4595_33721.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___4595_33721.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___4595_33721.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___4595_33721.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___4595_33721.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___4595_33721.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___4595_33721.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___4595_33721.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___4595_33721.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___4595_33721.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___4595_33721.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___4595_33721.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___4595_33721.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___4595_33721.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___4595_33721.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___4595_33721.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___4595_33721.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___4595_33721.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___4595_33721.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___4595_33721.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___4595_33721.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___4595_33721.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___4595_33721.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___4595_33721.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___4595_33721.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___4595_33721.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___4595_33721.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___4595_33721.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___4595_33721.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___4595_33721.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___4595_33721.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___4595_33721.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___4595_33721.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___4595_33721.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___4595_33721.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___4595_33721.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___4595_33721.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___4595_33721.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___4595_33721.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___4595_33721.FStar_TypeChecker_Env.erasable_types_tab);
                      FStar_TypeChecker_Env.enable_defer_to_tac = false
                    }  in
                  (env1.FStar_TypeChecker_Env.try_solve_implicits_hook env1
                     resolve_tac deferred_goals1;
                   guard))
          in
       let g1 = solve_deferred_constraints env g  in
       let g2 = solve_deferred_to_tactic g1  in
       (let uu____33727 = guard_to_string env g2  in
        FStar_Util.print1
          "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
          uu____33727);
       (let g3 = resolve_implicits env g2  in
        match g3.FStar_TypeChecker_Common.implicits with
        | [] ->
            let uu____33731 = discharge_guard env g3  in
            FStar_All.pipe_left (fun a2  -> ()) uu____33731
        | imp::uu____33733 ->
            let uu____33736 =
              let uu____33742 =
                let uu____33744 =
                  FStar_Syntax_Print.uvar_to_string
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                   in
                let uu____33746 =
                  FStar_TypeChecker_Normalize.term_to_string env
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                   in
                FStar_Util.format3
                  "Failed to resolve implicit argument %s of type %s introduced for %s"
                  uu____33744 uu____33746
                  imp.FStar_TypeChecker_Common.imp_reason
                 in
              (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____33742)
               in
            FStar_Errors.raise_error uu____33736
              imp.FStar_TypeChecker_Common.imp_range))
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33766 = teq env t1 t2  in
        force_trivial_guard env uu____33766
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33785 = teq_nosmt env t1 t2  in
        match uu____33785 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4619_33804 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4619_33804.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4619_33804.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4619_33804.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4619_33804.FStar_TypeChecker_Common.implicits)
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
        (let uu____33840 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____33840
         then
           let uu____33845 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____33847 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____33845
             uu____33847
         else ());
        (let uu____33852 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____33852 with
         | (prob,x,wl) ->
             let g =
               let uu____33871 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____33882  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____33871  in
             ((let uu____33904 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____33904
               then
                 let uu____33909 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____33911 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____33913 =
                   let uu____33915 = FStar_Util.must g  in
                   guard_to_string env uu____33915  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____33909 uu____33911 uu____33913
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
        let uu____33952 = check_subtyping env t1 t2  in
        match uu____33952 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____33971 =
              let uu____33972 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____33972 g  in
            FStar_Pervasives_Native.Some uu____33971
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33991 = check_subtyping env t1 t2  in
        match uu____33991 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____34010 =
              let uu____34011 =
                let uu____34012 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____34012]  in
              FStar_TypeChecker_Env.close_guard env uu____34011 g  in
            FStar_Pervasives_Native.Some uu____34010
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____34050 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____34050
         then
           let uu____34055 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____34057 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____34055
             uu____34057
         else ());
        (let uu____34062 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____34062 with
         | (prob,x,wl) ->
             let g =
               let uu____34077 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____34088  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____34077  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____34113 =
                      let uu____34114 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____34114]  in
                    FStar_TypeChecker_Env.close_guard env uu____34113 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____34155 = subtype_nosmt env t1 t2  in
        match uu____34155 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  