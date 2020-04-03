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
    match projectee with | TERM _0 -> true | uu____51 -> false
  
let (__proj__TERM__item___0 :
  uvi -> (FStar_Syntax_Syntax.ctx_uvar * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | TERM _0 -> _0 
let (uu___is_UNIV : uvi -> Prims.bool) =
  fun projectee  ->
    match projectee with | UNIV _0 -> true | uu____86 -> false
  
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
      (fun uu____685  ->
         match uu____685 with
         | (uu____701,m,p) ->
             let uu____712 = FStar_Thunk.force m  in (uu____712, p)) wl_def
  
let (as_wl_deferred :
  worklist ->
    FStar_TypeChecker_Common.deferred ->
      (Prims.int * lstring * FStar_TypeChecker_Common.prob) Prims.list)
  =
  fun wl  ->
    fun d  ->
      FStar_List.map
        (fun uu____764  ->
           match uu____764 with
           | (m,p) ->
               let uu____784 = FStar_Thunk.mkv m  in ((wl.ctr), uu____784, p))
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
                    let uu____877 = FStar_Syntax_Unionfind.fresh ()  in
                    {
                      FStar_Syntax_Syntax.ctx_uvar_head = uu____877;
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
                   (let uu____909 =
                      FStar_TypeChecker_Env.debug wl.tcenv
                        (FStar_Options.Other "ImplicitTrace")
                       in
                    if uu____909
                    then
                      let uu____913 =
                        FStar_Syntax_Print.uvar_to_string
                          ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                         in
                      FStar_Util.print1 "Just created uvar (Rel) {%s}\n"
                        uu____913
                    else ());
                   (ctx_uvar, t,
                     ((let uu___86_919 = wl  in
                       {
                         attempting = (uu___86_919.attempting);
                         wl_deferred = (uu___86_919.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___86_919.wl_deferred_to_tac);
                         ctr = (uu___86_919.ctr);
                         defer_ok = (uu___86_919.defer_ok);
                         smt_ok = (uu___86_919.smt_ok);
                         umax_heuristic_ok = (uu___86_919.umax_heuristic_ok);
                         tcenv = (uu___86_919.tcenv);
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
            let uu___92_952 = wl.tcenv  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___92_952.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___92_952.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___92_952.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___92_952.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___92_952.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___92_952.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___92_952.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___92_952.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___92_952.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___92_952.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___92_952.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___92_952.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___92_952.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___92_952.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___92_952.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___92_952.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___92_952.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___92_952.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___92_952.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___92_952.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___92_952.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___92_952.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___92_952.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___92_952.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___92_952.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___92_952.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___92_952.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___92_952.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___92_952.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___92_952.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___92_952.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___92_952.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___92_952.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___92_952.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___92_952.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___92_952.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___92_952.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___92_952.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___92_952.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___92_952.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___92_952.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___92_952.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___92_952.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___92_952.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___92_952.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___92_952.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___92_952.FStar_TypeChecker_Env.enable_defer_to_tac)
            }  in
          let env1 = FStar_TypeChecker_Env.push_binders env bs  in
          let uu____954 = FStar_TypeChecker_Env.all_binders env1  in
          new_uvar
            (Prims.op_Hat "copy:" u.FStar_Syntax_Syntax.ctx_uvar_reason) wl
            u.FStar_Syntax_Syntax.ctx_uvar_range
            env1.FStar_TypeChecker_Env.gamma uu____954 t
            u.FStar_Syntax_Syntax.ctx_uvar_should_check
            u.FStar_Syntax_Syntax.ctx_uvar_meta
  
type solution =
  | Success of (FStar_TypeChecker_Common.deferred *
  FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.implicits) 
  | Failed of (FStar_TypeChecker_Common.prob * lstring) 
let (uu___is_Success : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____1045 -> false
  
let (__proj__Success__item___0 :
  solution ->
    (FStar_TypeChecker_Common.deferred * FStar_TypeChecker_Common.deferred *
      FStar_TypeChecker_Common.implicits))
  = fun projectee  -> match projectee with | Success _0 -> _0 
let (uu___is_Failed : solution -> Prims.bool) =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____1086 -> false
  
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
        let uu___101_1123 = wl  in
        let uu____1124 =
          let uu____1134 = as_wl_deferred wl defer_to_tac  in
          FStar_List.append wl.wl_deferred_to_tac uu____1134  in
        {
          attempting = (uu___101_1123.attempting);
          wl_deferred = (uu___101_1123.wl_deferred);
          wl_deferred_to_tac = uu____1124;
          ctr = (uu___101_1123.ctr);
          defer_ok = (uu___101_1123.defer_ok);
          smt_ok = (uu___101_1123.smt_ok);
          umax_heuristic_ok = (uu___101_1123.umax_heuristic_ok);
          tcenv = (uu___101_1123.tcenv);
          wl_implicits = (FStar_List.append wl.wl_implicits imps)
        }
  
type variance =
  | COVARIANT 
  | CONTRAVARIANT 
  | INVARIANT 
let (uu___is_COVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | COVARIANT  -> true | uu____1160 -> false
  
let (uu___is_CONTRAVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | CONTRAVARIANT  -> true | uu____1171 -> false
  
let (uu___is_INVARIANT : variance -> Prims.bool) =
  fun projectee  ->
    match projectee with | INVARIANT  -> true | uu____1182 -> false
  
type tprob = FStar_Syntax_Syntax.typ FStar_TypeChecker_Common.problem
type cprob = FStar_Syntax_Syntax.comp FStar_TypeChecker_Common.problem
type 'a problem_t = 'a FStar_TypeChecker_Common.problem
let (rel_to_string : FStar_TypeChecker_Common.rel -> Prims.string) =
  fun uu___0_1200  ->
    match uu___0_1200 with
    | FStar_TypeChecker_Common.EQ  -> "="
    | FStar_TypeChecker_Common.SUB  -> "<:"
    | FStar_TypeChecker_Common.SUBINV  -> ":>"
  
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____1212 = FStar_Syntax_Util.head_and_args t  in
    match uu____1212 with
    | (head1,args) ->
        (match head1.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
             let uu____1275 = FStar_Syntax_Print.ctx_uvar_to_string u  in
             let uu____1277 =
               match FStar_Pervasives_Native.fst s with
               | [] -> ""
               | s1 ->
                   let uu____1292 =
                     let uu____1294 = FStar_List.hd s1  in
                     FStar_Syntax_Print.subst_to_string uu____1294  in
                   FStar_Util.format1 "@<%s>" uu____1292
                in
             let uu____1298 = FStar_Syntax_Print.args_to_string args  in
             FStar_Util.format3 "%s%s %s" uu____1275 uu____1277 uu____1298
         | uu____1301 -> FStar_Syntax_Print.term_to_string t)
  
let (prob_to_string :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Common.prob -> Prims.string)
  =
  fun env  ->
    fun uu___1_1313  ->
      match uu___1_1313 with
      | FStar_TypeChecker_Common.TProb p ->
          let uu____1318 =
            let uu____1322 =
              FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
            let uu____1324 =
              let uu____1328 = term_to_string p.FStar_TypeChecker_Common.lhs
                 in
              let uu____1330 =
                let uu____1334 =
                  let uu____1338 =
                    term_to_string p.FStar_TypeChecker_Common.rhs  in
                  [uu____1338]  in
                (rel_to_string p.FStar_TypeChecker_Common.relation) ::
                  uu____1334
                 in
              uu____1328 :: uu____1330  in
            uu____1322 :: uu____1324  in
          FStar_Util.format "\n%s:\t%s \n\t\t%s\n\t%s\n" uu____1318
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1349 =
            FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid  in
          let uu____1351 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.lhs
             in
          let uu____1353 =
            FStar_TypeChecker_Normalize.comp_to_string env
              p.FStar_TypeChecker_Common.rhs
             in
          FStar_Util.format4 "\n%s:\t%s \n\t\t%s\n\t%s" uu____1349 uu____1351
            (rel_to_string p.FStar_TypeChecker_Common.relation) uu____1353
  
let (uvi_to_string : FStar_TypeChecker_Env.env -> uvi -> Prims.string) =
  fun env  ->
    fun uu___2_1367  ->
      match uu___2_1367 with
      | UNIV (u,t) ->
          let x =
            let uu____1373 = FStar_Options.hide_uvar_nums ()  in
            if uu____1373
            then "?"
            else
              (let uu____1380 = FStar_Syntax_Unionfind.univ_uvar_id u  in
               FStar_All.pipe_right uu____1380 FStar_Util.string_of_int)
             in
          let uu____1384 = FStar_Syntax_Print.univ_to_string t  in
          FStar_Util.format2 "UNIV %s %s" x uu____1384
      | TERM (u,t) ->
          let x =
            let uu____1391 = FStar_Options.hide_uvar_nums ()  in
            if uu____1391
            then "?"
            else
              (let uu____1398 =
                 FStar_Syntax_Unionfind.uvar_id
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               FStar_All.pipe_right uu____1398 FStar_Util.string_of_int)
             in
          let uu____1402 = FStar_TypeChecker_Normalize.term_to_string env t
             in
          FStar_Util.format2 "TERM %s %s" x uu____1402
  
let (uvis_to_string :
  FStar_TypeChecker_Env.env -> uvi Prims.list -> Prims.string) =
  fun env  ->
    fun uvis  ->
      let uu____1421 = FStar_List.map (uvi_to_string env) uvis  in
      FStar_All.pipe_right uu____1421 (FStar_String.concat ", ")
  
let (names_to_string : FStar_Syntax_Syntax.bv FStar_Util.set -> Prims.string)
  =
  fun nms  ->
    let uu____1442 =
      let uu____1446 = FStar_Util.set_elements nms  in
      FStar_All.pipe_right uu____1446
        (FStar_List.map FStar_Syntax_Print.bv_to_string)
       in
    FStar_All.pipe_right uu____1442 (FStar_String.concat ", ")
  
let args_to_string :
  'Auu____1465 .
    (FStar_Syntax_Syntax.term * 'Auu____1465) Prims.list -> Prims.string
  =
  fun args  ->
    let uu____1484 =
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1505  ->
              match uu____1505 with
              | (x,uu____1512) -> FStar_Syntax_Print.term_to_string x))
       in
    FStar_All.pipe_right uu____1484 (FStar_String.concat " ")
  
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
        (let uu____1559 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____1559
         then
           let uu____1564 = FStar_Thunk.force reason  in
           let uu____1567 = prob_to_string env prob  in
           FStar_Util.print2 "Failed %s:\n%s\n" uu____1564 uu____1567
         else ());
        Failed (prob, reason)
  
let (giveup_lit :
  FStar_TypeChecker_Env.env ->
    Prims.string -> FStar_TypeChecker_Common.prob -> solution)
  =
  fun env  ->
    fun reason  ->
      fun prob  ->
        let uu____1590 = FStar_Thunk.mk (fun uu____1593  -> reason)  in
        giveup env uu____1590 prob
  
let (invert_rel :
  FStar_TypeChecker_Common.rel -> FStar_TypeChecker_Common.rel) =
  fun uu___3_1599  ->
    match uu___3_1599 with
    | FStar_TypeChecker_Common.EQ  -> FStar_TypeChecker_Common.EQ
    | FStar_TypeChecker_Common.SUB  -> FStar_TypeChecker_Common.SUBINV
    | FStar_TypeChecker_Common.SUBINV  -> FStar_TypeChecker_Common.SUB
  
let invert :
  'Auu____1605 .
    'Auu____1605 FStar_TypeChecker_Common.problem ->
      'Auu____1605 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    let uu___161_1617 = p  in
    {
      FStar_TypeChecker_Common.pid =
        (uu___161_1617.FStar_TypeChecker_Common.pid);
      FStar_TypeChecker_Common.lhs = (p.FStar_TypeChecker_Common.rhs);
      FStar_TypeChecker_Common.relation =
        (invert_rel p.FStar_TypeChecker_Common.relation);
      FStar_TypeChecker_Common.rhs = (p.FStar_TypeChecker_Common.lhs);
      FStar_TypeChecker_Common.element =
        (uu___161_1617.FStar_TypeChecker_Common.element);
      FStar_TypeChecker_Common.logical_guard =
        (uu___161_1617.FStar_TypeChecker_Common.logical_guard);
      FStar_TypeChecker_Common.logical_guard_uvar =
        (uu___161_1617.FStar_TypeChecker_Common.logical_guard_uvar);
      FStar_TypeChecker_Common.reason =
        (uu___161_1617.FStar_TypeChecker_Common.reason);
      FStar_TypeChecker_Common.loc =
        (uu___161_1617.FStar_TypeChecker_Common.loc);
      FStar_TypeChecker_Common.rank =
        (uu___161_1617.FStar_TypeChecker_Common.rank)
    }
  
let maybe_invert :
  'Auu____1625 .
    'Auu____1625 FStar_TypeChecker_Common.problem ->
      'Auu____1625 FStar_TypeChecker_Common.problem
  =
  fun p  ->
    if p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV
    then invert p
    else p
  
let (maybe_invert_p :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___4_1645  ->
    match uu___4_1645 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1651  -> FStar_TypeChecker_Common.TProb _1651)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_right (maybe_invert p)
          (fun _1657  -> FStar_TypeChecker_Common.CProb _1657)
  
let (make_prob_eq :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___5_1663  ->
    match uu___5_1663 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_TypeChecker_Common.TProb
          (let uu___173_1669 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___173_1669.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___173_1669.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___173_1669.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___173_1669.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___173_1669.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___173_1669.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___173_1669.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___173_1669.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___173_1669.FStar_TypeChecker_Common.rank)
           })
    | FStar_TypeChecker_Common.CProb p ->
        FStar_TypeChecker_Common.CProb
          (let uu___177_1677 = p  in
           {
             FStar_TypeChecker_Common.pid =
               (uu___177_1677.FStar_TypeChecker_Common.pid);
             FStar_TypeChecker_Common.lhs =
               (uu___177_1677.FStar_TypeChecker_Common.lhs);
             FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ;
             FStar_TypeChecker_Common.rhs =
               (uu___177_1677.FStar_TypeChecker_Common.rhs);
             FStar_TypeChecker_Common.element =
               (uu___177_1677.FStar_TypeChecker_Common.element);
             FStar_TypeChecker_Common.logical_guard =
               (uu___177_1677.FStar_TypeChecker_Common.logical_guard);
             FStar_TypeChecker_Common.logical_guard_uvar =
               (uu___177_1677.FStar_TypeChecker_Common.logical_guard_uvar);
             FStar_TypeChecker_Common.reason =
               (uu___177_1677.FStar_TypeChecker_Common.reason);
             FStar_TypeChecker_Common.loc =
               (uu___177_1677.FStar_TypeChecker_Common.loc);
             FStar_TypeChecker_Common.rank =
               (uu___177_1677.FStar_TypeChecker_Common.rank)
           })
  
let (vary_rel :
  FStar_TypeChecker_Common.rel -> variance -> FStar_TypeChecker_Common.rel) =
  fun rel  ->
    fun uu___6_1690  ->
      match uu___6_1690 with
      | INVARIANT  -> FStar_TypeChecker_Common.EQ
      | CONTRAVARIANT  -> invert_rel rel
      | COVARIANT  -> rel
  
let (p_pid : FStar_TypeChecker_Common.prob -> Prims.int) =
  fun uu___7_1697  ->
    match uu___7_1697 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.pid
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.pid
  
let (p_rel : FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.rel) =
  fun uu___8_1710  ->
    match uu___8_1710 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.relation
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.relation
  
let (p_reason : FStar_TypeChecker_Common.prob -> Prims.string Prims.list) =
  fun uu___9_1725  ->
    match uu___9_1725 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.reason
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.reason
  
let (p_loc : FStar_TypeChecker_Common.prob -> FStar_Range.range) =
  fun uu___10_1740  ->
    match uu___10_1740 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.loc
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.loc
  
let (p_element :
  FStar_TypeChecker_Common.prob ->
    FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  =
  fun uu___11_1754  ->
    match uu___11_1754 with
    | FStar_TypeChecker_Common.TProb p -> p.FStar_TypeChecker_Common.element
    | FStar_TypeChecker_Common.CProb p -> p.FStar_TypeChecker_Common.element
  
let (p_guard : FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term) =
  fun uu___12_1768  ->
    match uu___12_1768 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard
  
let (p_guard_uvar :
  FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.ctx_uvar) =
  fun uu___13_1780  ->
    match uu___13_1780 with
    | FStar_TypeChecker_Common.TProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
    | FStar_TypeChecker_Common.CProb p ->
        p.FStar_TypeChecker_Common.logical_guard_uvar
  
let def_scope_wf :
  'Auu____1796 .
    Prims.string ->
      FStar_Range.range ->
        (FStar_Syntax_Syntax.bv * 'Auu____1796) Prims.list -> unit
  =
  fun msg  ->
    fun rng  ->
      fun r  ->
        let uu____1826 =
          let uu____1828 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____1828  in
        if uu____1826
        then ()
        else
          (let rec aux prev next =
             match next with
             | [] -> ()
             | (bv,uu____1865)::bs ->
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
          let uu____1912 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1936 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1936]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1912
      | FStar_TypeChecker_Common.CProb p ->
          let uu____1964 =
            match p_element prob with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some x ->
                let uu____1988 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____1988]
             in
          FStar_List.append
            (p.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_binders
            uu____1964
       in
    def_scope_wf "p_scope" (p_loc prob) r; r
  
let (def_check_scoped :
  Prims.string ->
    FStar_TypeChecker_Common.prob -> FStar_Syntax_Syntax.term -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun phi  ->
        let uu____2035 =
          let uu____2037 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2037  in
        if uu____2035
        then ()
        else
          (let uu____2042 =
             let uu____2045 = p_scope prob  in
             FStar_All.pipe_left (FStar_List.map FStar_Pervasives_Native.fst)
               uu____2045
              in
           FStar_TypeChecker_Env.def_check_closed_in (p_loc prob) msg
             uu____2042 phi)
  
let (def_check_scoped_comp :
  Prims.string ->
    FStar_TypeChecker_Common.prob ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit)
  =
  fun msg  ->
    fun prob  ->
      fun comp  ->
        let uu____2094 =
          let uu____2096 = FStar_Options.defensive ()  in
          Prims.op_Negation uu____2096  in
        if uu____2094
        then ()
        else
          (let uu____2101 = FStar_Syntax_Util.arrow [] comp  in
           def_check_scoped msg prob uu____2101)
  
let (def_check_prob : Prims.string -> FStar_TypeChecker_Common.prob -> unit)
  =
  fun msg  ->
    fun prob  ->
      let uu____2121 =
        let uu____2123 = FStar_Options.defensive ()  in
        Prims.op_Negation uu____2123  in
      if uu____2121
      then ()
      else
        (let msgf m =
           let uu____2137 =
             let uu____2139 =
               let uu____2141 = FStar_Util.string_of_int (p_pid prob)  in
               Prims.op_Hat uu____2141 (Prims.op_Hat "." m)  in
             Prims.op_Hat "." uu____2139  in
           Prims.op_Hat msg uu____2137  in
         (let uu____2146 = msgf "scope"  in
          let uu____2149 = p_scope prob  in
          def_scope_wf uu____2146 (p_loc prob) uu____2149);
         (let uu____2161 = msgf "guard"  in
          def_check_scoped uu____2161 prob (p_guard prob));
         (match prob with
          | FStar_TypeChecker_Common.TProb p ->
              ((let uu____2168 = msgf "lhs"  in
                def_check_scoped uu____2168 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2171 = msgf "rhs"  in
                def_check_scoped uu____2171 prob
                  p.FStar_TypeChecker_Common.rhs))
          | FStar_TypeChecker_Common.CProb p ->
              ((let uu____2178 = msgf "lhs"  in
                def_check_scoped_comp uu____2178 prob
                  p.FStar_TypeChecker_Common.lhs);
               (let uu____2181 = msgf "rhs"  in
                def_check_scoped_comp uu____2181 prob
                  p.FStar_TypeChecker_Common.rhs))))
  
let (singleton :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.bool -> worklist) =
  fun wl  ->
    fun prob  ->
      fun smt_ok  ->
        let uu___270_2202 = wl  in
        {
          attempting = [prob];
          wl_deferred = (uu___270_2202.wl_deferred);
          wl_deferred_to_tac = (uu___270_2202.wl_deferred_to_tac);
          ctr = (uu___270_2202.ctr);
          defer_ok = (uu___270_2202.defer_ok);
          smt_ok;
          umax_heuristic_ok = (uu___270_2202.umax_heuristic_ok);
          tcenv = (uu___270_2202.tcenv);
          wl_implicits = (uu___270_2202.wl_implicits)
        }
  
let wl_of_guard :
  'Auu____2210 .
    FStar_TypeChecker_Env.env ->
      ('Auu____2210 * FStar_TypeChecker_Common.prob) Prims.list -> worklist
  =
  fun env  ->
    fun g  ->
      let uu___274_2233 = empty_worklist env  in
      let uu____2234 = FStar_List.map FStar_Pervasives_Native.snd g  in
      {
        attempting = uu____2234;
        wl_deferred = (uu___274_2233.wl_deferred);
        wl_deferred_to_tac = (uu___274_2233.wl_deferred_to_tac);
        ctr = (uu___274_2233.ctr);
        defer_ok = (uu___274_2233.defer_ok);
        smt_ok = (uu___274_2233.smt_ok);
        umax_heuristic_ok = (uu___274_2233.umax_heuristic_ok);
        tcenv = (uu___274_2233.tcenv);
        wl_implicits = (uu___274_2233.wl_implicits)
      }
  
let (defer :
  lstring -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu___279_2255 = wl  in
        {
          attempting = (uu___279_2255.attempting);
          wl_deferred = (((wl.ctr), reason, prob) :: (wl.wl_deferred));
          wl_deferred_to_tac = (uu___279_2255.wl_deferred_to_tac);
          ctr = (uu___279_2255.ctr);
          defer_ok = (uu___279_2255.defer_ok);
          smt_ok = (uu___279_2255.smt_ok);
          umax_heuristic_ok = (uu___279_2255.umax_heuristic_ok);
          tcenv = (uu___279_2255.tcenv);
          wl_implicits = (uu___279_2255.wl_implicits)
        }
  
let (defer_lit :
  Prims.string -> FStar_TypeChecker_Common.prob -> worklist -> worklist) =
  fun reason  ->
    fun prob  ->
      fun wl  ->
        let uu____2282 = FStar_Thunk.mkv reason  in defer uu____2282 prob wl
  
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
      | uu____2314 -> FStar_Pervasives_Native.None
  
let (should_defer_uvar_to_user_tac :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.ctx_uvar -> Prims.bool) =
  fun env  ->
    fun u  ->
      if Prims.op_Negation env.FStar_TypeChecker_Env.enable_defer_to_tac
      then false
      else
        (let uu____2334 = find_user_tac_for_uvar env u  in
         FStar_Option.isSome uu____2334)
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___298_2354 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___298_2354.wl_deferred);
         wl_deferred_to_tac = (uu___298_2354.wl_deferred_to_tac);
         ctr = (uu___298_2354.ctr);
         defer_ok = (uu___298_2354.defer_ok);
         smt_ok = (uu___298_2354.smt_ok);
         umax_heuristic_ok = (uu___298_2354.umax_heuristic_ok);
         tcenv = (uu___298_2354.tcenv);
         wl_implicits = (uu___298_2354.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____2368 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2368 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____2402 = FStar_Syntax_Util.type_u ()  in
            match uu____2402 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____2414 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____2414 with
                 | (uu____2426,tt,wl1) ->
                     let uu____2429 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2429, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2435  ->
    match uu___14_2435 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _2441  -> FStar_TypeChecker_Common.TProb _2441) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _2447  -> FStar_TypeChecker_Common.CProb _2447) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2455 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2455 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2475  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2517 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2517 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2517 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2517 FStar_TypeChecker_Common.problem *
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
                        let uu____2604 =
                          let uu____2613 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2613]  in
                        FStar_List.append scope uu____2604
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2656 =
                      let uu____2659 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2659  in
                    FStar_List.append uu____2656
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2678 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2678 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2698 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2698;
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
                  (let uu____2772 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2772 with
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
                  (let uu____2860 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2860 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2898 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2898 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2898 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2898 FStar_TypeChecker_Common.problem *
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
                          let uu____2966 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2966]  in
                        let uu____2985 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2985
                     in
                  let uu____2988 =
                    let uu____2995 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___381_3006 = wl  in
                       {
                         attempting = (uu___381_3006.attempting);
                         wl_deferred = (uu___381_3006.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___381_3006.wl_deferred_to_tac);
                         ctr = (uu___381_3006.ctr);
                         defer_ok = (uu___381_3006.defer_ok);
                         smt_ok = (uu___381_3006.smt_ok);
                         umax_heuristic_ok =
                           (uu___381_3006.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___381_3006.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2995
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2988 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____3018 =
                              let uu____3023 =
                                let uu____3024 =
                                  let uu____3033 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____3033
                                   in
                                [uu____3024]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____3023  in
                            uu____3018 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____3061 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____3061;
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
                let uu____3109 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____3109;
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
  'Auu____3124 .
    worklist ->
      'Auu____3124 FStar_TypeChecker_Common.problem ->
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
              let uu____3157 =
                let uu____3160 =
                  let uu____3161 =
                    let uu____3168 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____3168)  in
                  FStar_Syntax_Syntax.NT uu____3161  in
                [uu____3160]  in
              FStar_Syntax_Subst.subst uu____3157 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____3190 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____3190
        then
          let uu____3198 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____3201 = prob_to_string env d  in
          let uu____3203 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____3210 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3198 uu____3201 uu____3203 uu____3210
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____3222 -> failwith "impossible"  in
           let uu____3225 =
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
           match uu____3225 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3268  ->
            match uu___15_3268 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3280 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____3284 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3284 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_3315  ->
           match uu___16_3315 with
           | UNIV uu____3318 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____3325 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____3325
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
        (fun uu___17_3353  ->
           match uu___17_3353 with
           | UNIV (u',t) ->
               let uu____3358 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____3358
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3365 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3377 =
        let uu____3378 =
          let uu____3379 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3379
           in
        FStar_Syntax_Subst.compress uu____3378  in
      FStar_All.pipe_right uu____3377 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3391 =
        let uu____3392 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3392  in
      FStar_All.pipe_right uu____3391 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3404 =
        let uu____3408 =
          let uu____3410 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3410  in
        FStar_Pervasives_Native.Some uu____3408  in
      FStar_Profiling.profile (fun uu____3413  -> sn' env t) uu____3404
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
          let uu____3438 =
            let uu____3442 =
              let uu____3444 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3444  in
            FStar_Pervasives_Native.Some uu____3442  in
          FStar_Profiling.profile
            (fun uu____3447  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3438
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3455 = FStar_Syntax_Util.head_and_args t  in
    match uu____3455 with
    | (h,uu____3474) ->
        let uu____3499 =
          let uu____3500 = FStar_Syntax_Subst.compress h  in
          uu____3500.FStar_Syntax_Syntax.n  in
        (match uu____3499 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3505 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3518 =
        let uu____3522 =
          let uu____3524 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3524  in
        FStar_Pervasives_Native.Some uu____3522  in
      FStar_Profiling.profile
        (fun uu____3529  ->
           let uu____3530 = should_strongly_reduce t  in
           if uu____3530
           then
             let uu____3533 =
               let uu____3534 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3534  in
             FStar_All.pipe_right uu____3533 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3518 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3545 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3545) ->
        (FStar_Syntax_Syntax.term * 'Auu____3545)
  =
  fun env  ->
    fun t  ->
      let uu____3568 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3568, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3620  ->
              match uu____3620 with
              | (x,imp) ->
                  let uu____3639 =
                    let uu___487_3640 = x  in
                    let uu____3641 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___487_3640.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___487_3640.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3641
                    }  in
                  (uu____3639, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3665 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3665
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3669 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3669
        | uu____3672 -> u2  in
      let uu____3673 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3673
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3690 =
          let uu____3694 =
            let uu____3696 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3696  in
          FStar_Pervasives_Native.Some uu____3694  in
        FStar_Profiling.profile
          (fun uu____3699  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3690 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3821 = norm_refinement env t12  in
                 match uu____3821 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3836;
                     FStar_Syntax_Syntax.vars = uu____3837;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3861 =
                       let uu____3863 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3865 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3863 uu____3865
                        in
                     failwith uu____3861)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3881 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3881
          | FStar_Syntax_Syntax.Tm_uinst uu____3882 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3919 =
                   let uu____3920 = FStar_Syntax_Subst.compress t1'  in
                   uu____3920.FStar_Syntax_Syntax.n  in
                 match uu____3919 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3935 -> aux true t1'
                 | uu____3943 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3958 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3989 =
                   let uu____3990 = FStar_Syntax_Subst.compress t1'  in
                   uu____3990.FStar_Syntax_Syntax.n  in
                 match uu____3989 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4005 -> aux true t1'
                 | uu____4013 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4028 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4075 =
                   let uu____4076 = FStar_Syntax_Subst.compress t1'  in
                   uu____4076.FStar_Syntax_Syntax.n  in
                 match uu____4075 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4091 -> aux true t1'
                 | uu____4099 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____4114 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____4129 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____4144 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____4159 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____4174 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____4203 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____4236 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____4257 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____4284 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____4312 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____4349 ->
              let uu____4356 =
                let uu____4358 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4360 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4358 uu____4360
                 in
              failwith uu____4356
          | FStar_Syntax_Syntax.Tm_ascribed uu____4375 ->
              let uu____4402 =
                let uu____4404 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4406 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4404 uu____4406
                 in
              failwith uu____4402
          | FStar_Syntax_Syntax.Tm_delayed uu____4421 ->
              let uu____4436 =
                let uu____4438 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4440 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4438 uu____4440
                 in
              failwith uu____4436
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4455 =
                let uu____4457 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4459 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4457 uu____4459
                 in
              failwith uu____4455
           in
        let uu____4474 = whnf env t1  in aux false uu____4474
  
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
      let uu____4519 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4519 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4560 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4560, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4587 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4587 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4647  ->
    match uu____4647 with
    | (t_base,refopt) ->
        let uu____4678 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4678 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4720 =
      let uu____4724 =
        let uu____4727 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4752  ->
                  match uu____4752 with | (uu____4760,uu____4761,x) -> x))
           in
        FStar_List.append wl.attempting uu____4727  in
      FStar_List.map (wl_prob_to_string wl) uu____4724  in
    FStar_All.pipe_right uu____4720 (FStar_String.concat "\n\t")
  
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
  fun uu____4821  ->
    match uu____4821 with
    | Flex (uu____4823,u,uu____4825) -> u.FStar_Syntax_Syntax.ctx_uvar_reason
  
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4832  ->
    match uu____4832 with
    | Flex (uu____4834,c,args) ->
        let uu____4837 = print_ctx_uvar c  in
        let uu____4839 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4837 uu____4839
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4849 = FStar_Syntax_Util.head_and_args t  in
    match uu____4849 with
    | (head1,_args) ->
        let uu____4893 =
          let uu____4894 = FStar_Syntax_Subst.compress head1  in
          uu____4894.FStar_Syntax_Syntax.n  in
        (match uu____4893 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4898 -> true
         | uu____4912 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4920 = FStar_Syntax_Util.head_and_args t  in
    match uu____4920 with
    | (head1,_args) ->
        let uu____4963 =
          let uu____4964 = FStar_Syntax_Subst.compress head1  in
          uu____4964.FStar_Syntax_Syntax.n  in
        (match uu____4963 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4968) -> u
         | uu____4985 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____5010 = FStar_Syntax_Util.head_and_args t  in
      match uu____5010 with
      | (head1,args) ->
          let uu____5057 =
            let uu____5058 = FStar_Syntax_Subst.compress head1  in
            uu____5058.FStar_Syntax_Syntax.n  in
          (match uu____5057 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____5066)) ->
               ((Flex (t, uv, args)), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____5099 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_5124  ->
                         match uu___18_5124 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____5129 =
                               let uu____5130 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____5130.FStar_Syntax_Syntax.n  in
                             (match uu____5129 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____5135 -> false)
                         | uu____5137 -> true))
                  in
               (match uu____5099 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____5162 =
                        FStar_List.collect
                          (fun uu___19_5174  ->
                             match uu___19_5174 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____5178 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____5178]
                             | uu____5179 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____5162 FStar_List.rev  in
                    let uu____5202 =
                      let uu____5209 =
                        let uu____5218 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_5240  ->
                                  match uu___20_5240 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____5244 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____5244]
                                  | uu____5245 -> []))
                           in
                        FStar_All.pipe_right uu____5218 FStar_List.rev  in
                      let uu____5268 =
                        let uu____5271 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____5271  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____5209 uu____5268
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____5202 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____5307  ->
                                match uu____5307 with
                                | (x,i) ->
                                    let uu____5326 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____5326, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____5357  ->
                                match uu____5357 with
                                | (a,i) ->
                                    let uu____5376 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____5376, i)) args_sol
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
           | uu____5398 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5420 =
          let uu____5443 =
            let uu____5444 = FStar_Syntax_Subst.compress k  in
            uu____5444.FStar_Syntax_Syntax.n  in
          match uu____5443 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5526 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5526)
              else
                (let uu____5561 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5561 with
                 | (ys',t1,uu____5594) ->
                     let uu____5599 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5599))
          | uu____5638 ->
              let uu____5639 =
                let uu____5644 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5644)  in
              ((ys, t), uu____5639)
           in
        match uu____5420 with
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
                 let uu____5739 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5739 c  in
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
               (let uu____5817 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5817
                then
                  let uu____5822 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5824 = print_ctx_uvar uv  in
                  let uu____5826 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5822 uu____5824 uu____5826
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5835 =
                   let uu____5837 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5837  in
                 let uu____5840 =
                   let uu____5843 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5843
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5835 uu____5840 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5876 =
               let uu____5877 =
                 let uu____5879 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5881 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5879 uu____5881
                  in
               failwith uu____5877  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5947  ->
                       match uu____5947 with
                       | (a,i) ->
                           let uu____5968 =
                             let uu____5969 = FStar_Syntax_Subst.compress a
                                in
                             uu____5969.FStar_Syntax_Syntax.n  in
                           (match uu____5968 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5995 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____6005 =
                 let uu____6007 = is_flex g  in Prims.op_Negation uu____6007
                  in
               if uu____6005
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____6016 = destruct_flex_t g wl  in
                  match uu____6016 with
                  | (Flex (uu____6021,uv1,args),wl1) ->
                      ((let uu____6026 = args_as_binders args  in
                        assign_solution uu____6026 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___749_6028 = wl1  in
              {
                attempting = (uu___749_6028.attempting);
                wl_deferred = (uu___749_6028.wl_deferred);
                wl_deferred_to_tac = (uu___749_6028.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___749_6028.defer_ok);
                smt_ok = (uu___749_6028.smt_ok);
                umax_heuristic_ok = (uu___749_6028.umax_heuristic_ok);
                tcenv = (uu___749_6028.tcenv);
                wl_implicits = (uu___749_6028.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____6053 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____6053
         then
           let uu____6058 = FStar_Util.string_of_int pid  in
           let uu____6060 =
             let uu____6062 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____6062 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6058 uu____6060
         else ());
        commit sol;
        (let uu___757_6076 = wl  in
         {
           attempting = (uu___757_6076.attempting);
           wl_deferred = (uu___757_6076.wl_deferred);
           wl_deferred_to_tac = (uu___757_6076.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___757_6076.defer_ok);
           smt_ok = (uu___757_6076.smt_ok);
           umax_heuristic_ok = (uu___757_6076.umax_heuristic_ok);
           tcenv = (uu___757_6076.tcenv);
           wl_implicits = (uu___757_6076.wl_implicits)
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
          (let uu____6112 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____6112
           then
             let uu____6117 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____6121 =
               let uu____6123 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____6123 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6117 uu____6121
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
        let uu____6158 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____6158 FStar_Util.set_elements  in
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
      let uu____6198 = occurs uk t  in
      match uu____6198 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6237 =
                 let uu____6239 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____6241 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6239 uu____6241
                  in
               FStar_Pervasives_Native.Some uu____6237)
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
            let uu____6361 = maximal_prefix bs_tail bs'_tail  in
            (match uu____6361 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6412 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6469  ->
             match uu____6469 with
             | (x,uu____6481) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6499 = FStar_List.last bs  in
      match uu____6499 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6523) ->
          let uu____6534 =
            FStar_Util.prefix_until
              (fun uu___21_6549  ->
                 match uu___21_6549 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6552 -> false) g
             in
          (match uu____6534 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6566,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6603 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6603 with
        | (pfx,uu____6613) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6625 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6625 with
             | (uu____6633,src',wl1) ->
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
                 | uu____6747 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6748 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6812  ->
                  fun uu____6813  ->
                    match (uu____6812, uu____6813) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6916 =
                          let uu____6918 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6918
                           in
                        if uu____6916
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6952 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6952
                           then
                             let uu____6969 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6969)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6748 with | (isect,uu____7019) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____7055 'Auu____7056 .
    (FStar_Syntax_Syntax.bv * 'Auu____7055) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____7056) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7114  ->
              fun uu____7115  ->
                match (uu____7114, uu____7115) with
                | ((a,uu____7134),(b,uu____7136)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____7152 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____7152) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____7183  ->
           match uu____7183 with
           | (y,uu____7190) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____7200 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____7200) Prims.list ->
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
                   let uu____7362 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____7362
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7395 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7447 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7491 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7512 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7520  ->
    match uu___22_7520 with
    | MisMatch (d1,d2) ->
        let uu____7532 =
          let uu____7534 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7536 =
            let uu____7538 =
              let uu____7540 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7540 ")"  in
            Prims.op_Hat ") (" uu____7538  in
          Prims.op_Hat uu____7534 uu____7536  in
        Prims.op_Hat "MisMatch (" uu____7532
    | HeadMatch u ->
        let uu____7547 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7547
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7556  ->
    match uu___23_7556 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7573 -> HeadMatch false
  
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
          let uu____7595 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7595 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7606 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7630 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7640 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7659 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7659
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7660 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7661 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7662 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7675 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7689 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7713) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7719,uu____7720) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7762) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7787;
             FStar_Syntax_Syntax.index = uu____7788;
             FStar_Syntax_Syntax.sort = t2;_},uu____7790)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7798 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7799 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7800 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7815 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7822 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7842 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7842
  
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
           { FStar_Syntax_Syntax.blob = uu____7861;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7862;
             FStar_Syntax_Syntax.ltyp = uu____7863;
             FStar_Syntax_Syntax.rng = uu____7864;_},uu____7865)
            ->
            let uu____7876 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7876 t21
        | (uu____7877,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7878;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7879;
             FStar_Syntax_Syntax.ltyp = uu____7880;
             FStar_Syntax_Syntax.rng = uu____7881;_})
            ->
            let uu____7892 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7892
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7904 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7904
            then FullMatch
            else
              (let uu____7909 =
                 let uu____7918 =
                   let uu____7921 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7921  in
                 let uu____7922 =
                   let uu____7925 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7925  in
                 (uu____7918, uu____7922)  in
               MisMatch uu____7909)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7931),FStar_Syntax_Syntax.Tm_uinst (g,uu____7933)) ->
            let uu____7942 = head_matches env f g  in
            FStar_All.pipe_right uu____7942 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7943) -> HeadMatch true
        | (uu____7945,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7949 = FStar_Const.eq_const c d  in
            if uu____7949
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7959),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7961)) ->
            let uu____7994 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7994
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____8004),FStar_Syntax_Syntax.Tm_refine (y,uu____8006)) ->
            let uu____8015 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8015 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____8017),uu____8018) ->
            let uu____8023 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____8023 head_match
        | (uu____8024,FStar_Syntax_Syntax.Tm_refine (x,uu____8026)) ->
            let uu____8031 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8031 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8032,FStar_Syntax_Syntax.Tm_type
           uu____8033) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____8035,FStar_Syntax_Syntax.Tm_arrow uu____8036) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____8067),FStar_Syntax_Syntax.Tm_app (head',uu____8069))
            ->
            let uu____8118 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____8118 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____8120),uu____8121) ->
            let uu____8146 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____8146 head_match
        | (uu____8147,FStar_Syntax_Syntax.Tm_app (head1,uu____8149)) ->
            let uu____8174 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____8174 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8175,FStar_Syntax_Syntax.Tm_let
           uu____8176) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____8204,FStar_Syntax_Syntax.Tm_match uu____8205) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8251,FStar_Syntax_Syntax.Tm_abs
           uu____8252) -> HeadMatch true
        | uu____8290 ->
            let uu____8295 =
              let uu____8304 = delta_depth_of_term env t11  in
              let uu____8307 = delta_depth_of_term env t21  in
              (uu____8304, uu____8307)  in
            MisMatch uu____8295
  
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
              let uu____8376 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8376  in
            (let uu____8378 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8378
             then
               let uu____8383 = FStar_Syntax_Print.term_to_string t  in
               let uu____8385 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8383 uu____8385
             else ());
            (let uu____8390 =
               let uu____8391 = FStar_Syntax_Util.un_uinst head1  in
               uu____8391.FStar_Syntax_Syntax.n  in
             match uu____8390 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8397 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8397 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8411 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8411
                        then
                          let uu____8416 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8416
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8421 ->
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
                      let uu____8439 =
                        let uu____8441 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8441 = FStar_Syntax_Util.Equal  in
                      if uu____8439
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8448 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8448
                          then
                            let uu____8453 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8455 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8453
                              uu____8455
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8460 -> FStar_Pervasives_Native.None)
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
            (let uu____8612 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8612
             then
               let uu____8617 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8619 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8621 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8617
                 uu____8619 uu____8621
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8649 =
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
               match uu____8649 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8697 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8697 with
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
                  uu____8735),uu____8736)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8757 =
                      let uu____8766 = maybe_inline t11  in
                      let uu____8769 = maybe_inline t21  in
                      (uu____8766, uu____8769)  in
                    match uu____8757 with
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
                 (uu____8812,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8813))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8834 =
                      let uu____8843 = maybe_inline t11  in
                      let uu____8846 = maybe_inline t21  in
                      (uu____8843, uu____8846)  in
                    match uu____8834 with
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
             | MisMatch uu____8901 -> fail1 n_delta r t11 t21
             | uu____8910 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8925 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8925
           then
             let uu____8930 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8932 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8934 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8942 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8959 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8959
                    (fun uu____8994  ->
                       match uu____8994 with
                       | (t11,t21) ->
                           let uu____9002 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____9004 =
                             let uu____9006 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____9006  in
                           Prims.op_Hat uu____9002 uu____9004))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8930 uu____8932 uu____8934 uu____8942
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____9023 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____9023 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_9038  ->
    match uu___24_9038 with
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
      let uu___1246_9087 = p  in
      let uu____9090 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____9091 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1246_9087.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9090;
        FStar_TypeChecker_Common.relation =
          (uu___1246_9087.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9091;
        FStar_TypeChecker_Common.element =
          (uu___1246_9087.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1246_9087.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1246_9087.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1246_9087.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1246_9087.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1246_9087.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9106 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____9106
            (fun _9111  -> FStar_TypeChecker_Common.TProb _9111)
      | FStar_TypeChecker_Common.CProb uu____9112 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____9135 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____9135 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9143 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9143 with
           | (lh,lhs_args) ->
               let uu____9190 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9190 with
                | (rh,rhs_args) ->
                    let uu____9237 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9250,FStar_Syntax_Syntax.Tm_uvar uu____9251)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9340 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9367,uu____9368)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9383,FStar_Syntax_Syntax.Tm_uvar uu____9384)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9399,FStar_Syntax_Syntax.Tm_arrow uu____9400)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1297_9430 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1297_9430.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1297_9430.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1297_9430.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1297_9430.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1297_9430.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1297_9430.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1297_9430.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1297_9430.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1297_9430.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9433,FStar_Syntax_Syntax.Tm_type uu____9434)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1297_9450 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1297_9450.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1297_9450.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1297_9450.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1297_9450.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1297_9450.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1297_9450.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1297_9450.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1297_9450.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1297_9450.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9453,FStar_Syntax_Syntax.Tm_uvar uu____9454)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1297_9470 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1297_9470.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1297_9470.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1297_9470.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1297_9470.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1297_9470.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1297_9470.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1297_9470.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1297_9470.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1297_9470.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9473,FStar_Syntax_Syntax.Tm_uvar uu____9474)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9489,uu____9490)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9505,FStar_Syntax_Syntax.Tm_uvar uu____9506)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9521,uu____9522) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9237 with
                     | (rank,tp1) ->
                         let uu____9535 =
                           FStar_All.pipe_right
                             (let uu___1317_9539 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1317_9539.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1317_9539.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1317_9539.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1317_9539.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1317_9539.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1317_9539.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1317_9539.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1317_9539.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1317_9539.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9542  ->
                                FStar_TypeChecker_Common.TProb _9542)
                            in
                         (rank, uu____9535))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9546 =
            FStar_All.pipe_right
              (let uu___1321_9550 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1321_9550.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1321_9550.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1321_9550.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1321_9550.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1321_9550.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1321_9550.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1321_9550.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1321_9550.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1321_9550.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9553  -> FStar_TypeChecker_Common.CProb _9553)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9546)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9613 probs =
      match uu____9613 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9694 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9715 = rank wl.tcenv hd1  in
               (match uu____9715 with
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
                      (let uu____9776 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9781 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9781)
                          in
                       if uu____9776
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
          let uu____9854 = FStar_Syntax_Util.head_and_args t  in
          match uu____9854 with
          | (hd1,uu____9873) ->
              let uu____9898 =
                let uu____9899 = FStar_Syntax_Subst.compress hd1  in
                uu____9899.FStar_Syntax_Syntax.n  in
              (match uu____9898 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9904) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9939  ->
                           match uu____9939 with
                           | (y,uu____9948) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9971  ->
                                       match uu____9971 with
                                       | (x,uu____9980) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9985 -> false)
           in
        let uu____9987 = rank tcenv p  in
        match uu____9987 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9996 -> true
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
    match projectee with | UDeferred _0 -> true | uu____10077 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____10096 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____10115 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____10132 = FStar_Thunk.mkv s  in UFailed uu____10132 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____10147 = FStar_Thunk.mk s  in UFailed uu____10147 
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
                        let uu____10199 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____10199 with
                        | (k,uu____10207) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10220 -> false)))
            | uu____10222 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10274 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____10282 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____10282 = Prims.int_zero))
                           in
                        if uu____10274 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____10303 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____10311 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____10311 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____10303)
               in
            let uu____10315 = filter1 u12  in
            let uu____10318 = filter1 u22  in (uu____10315, uu____10318)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10353 = filter_out_common_univs us1 us2  in
                   (match uu____10353 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10413 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10413 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10416 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10433  ->
                               let uu____10434 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10436 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10434 uu____10436))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10462 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10462 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10488 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10488 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10491 ->
                   ufailed_thunk
                     (fun uu____10502  ->
                        let uu____10503 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10505 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10503 uu____10505 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10508,uu____10509) ->
              let uu____10511 =
                let uu____10513 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10515 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10513 uu____10515
                 in
              failwith uu____10511
          | (FStar_Syntax_Syntax.U_unknown ,uu____10518) ->
              let uu____10519 =
                let uu____10521 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10523 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10521 uu____10523
                 in
              failwith uu____10519
          | (uu____10526,FStar_Syntax_Syntax.U_bvar uu____10527) ->
              let uu____10529 =
                let uu____10531 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10533 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10531 uu____10533
                 in
              failwith uu____10529
          | (uu____10536,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10537 =
                let uu____10539 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10541 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10539 uu____10541
                 in
              failwith uu____10537
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10571 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10571
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10588 = occurs_univ v1 u3  in
              if uu____10588
              then
                let uu____10591 =
                  let uu____10593 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10595 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10593 uu____10595
                   in
                try_umax_components u11 u21 uu____10591
              else
                (let uu____10600 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10600)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10612 = occurs_univ v1 u3  in
              if uu____10612
              then
                let uu____10615 =
                  let uu____10617 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10619 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10617 uu____10619
                   in
                try_umax_components u11 u21 uu____10615
              else
                (let uu____10624 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10624)
          | (FStar_Syntax_Syntax.U_max uu____10625,uu____10626) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10634 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10634
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10640,FStar_Syntax_Syntax.U_max uu____10641) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10649 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10649
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10655,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10657,FStar_Syntax_Syntax.U_name uu____10658) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10660) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10662) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10664,FStar_Syntax_Syntax.U_succ uu____10665) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10667,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10774 = bc1  in
      match uu____10774 with
      | (bs1,mk_cod1) ->
          let uu____10818 = bc2  in
          (match uu____10818 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10929 = aux xs ys  in
                     (match uu____10929 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____11012 =
                       let uu____11019 = mk_cod1 xs  in ([], uu____11019)  in
                     let uu____11022 =
                       let uu____11029 = mk_cod2 ys  in ([], uu____11029)  in
                     (uu____11012, uu____11022)
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
                  let uu____11098 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____11098 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____11101 =
                    let uu____11102 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____11102 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____11101
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____11107 = has_type_guard t1 t2  in (uu____11107, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____11108 = has_type_guard t2 t1  in (uu____11108, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___25_11115  ->
    match uu___25_11115 with
    | Flex (uu____11117,uu____11118,[]) -> true
    | uu____11128 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____11142 = f  in
      match uu____11142 with
      | Flex (uu____11144,u,uu____11146) ->
          should_defer_uvar_to_user_tac wl.tcenv u
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____11170 = f  in
      match uu____11170 with
      | Flex
          (uu____11177,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____11178;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11179;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____11182;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____11183;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____11184;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____11185;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11249  ->
                 match uu____11249 with
                 | (y,uu____11258) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11412 =
                  let uu____11427 =
                    let uu____11430 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11430  in
                  ((FStar_List.rev pat_binders), uu____11427)  in
                FStar_Pervasives_Native.Some uu____11412
            | (uu____11463,[]) ->
                let uu____11494 =
                  let uu____11509 =
                    let uu____11512 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11512  in
                  ((FStar_List.rev pat_binders), uu____11509)  in
                FStar_Pervasives_Native.Some uu____11494
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11603 =
                  let uu____11604 = FStar_Syntax_Subst.compress a  in
                  uu____11604.FStar_Syntax_Syntax.n  in
                (match uu____11603 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11624 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11624
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1658_11654 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1658_11654.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1658_11654.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11658 =
                            let uu____11659 =
                              let uu____11666 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11666)  in
                            FStar_Syntax_Syntax.NT uu____11659  in
                          [uu____11658]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1664_11682 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1664_11682.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1664_11682.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11683 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11723 =
                  let uu____11730 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11730  in
                (match uu____11723 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11789 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11814 ->
               let uu____11815 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11815 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____12147 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____12147
       then
         let uu____12152 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12152
       else ());
      (let uu____12158 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____12158
       then
         let uu____12163 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12163
       else ());
      (let uu____12168 = next_prob probs  in
       match uu____12168 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1691_12195 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1691_12195.wl_deferred);
               wl_deferred_to_tac = (uu___1691_12195.wl_deferred_to_tac);
               ctr = (uu___1691_12195.ctr);
               defer_ok = (uu___1691_12195.defer_ok);
               smt_ok = (uu___1691_12195.smt_ok);
               umax_heuristic_ok = (uu___1691_12195.umax_heuristic_ok);
               tcenv = (uu___1691_12195.tcenv);
               wl_implicits = (uu___1691_12195.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12204 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____12204
                 then
                   let uu____12207 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____12207
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
                           (let uu___1703_12219 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1703_12219.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1703_12219.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1703_12219.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1703_12219.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1703_12219.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1703_12219.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1703_12219.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1703_12219.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1703_12219.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12239 =
                  let uu____12246 = as_deferred probs.wl_deferred_to_tac  in
                  ([], uu____12246, (probs.wl_implicits))  in
                Success uu____12239
            | uu____12252 ->
                let uu____12262 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12327  ->
                          match uu____12327 with
                          | (c,uu____12337,uu____12338) -> c < probs.ctr))
                   in
                (match uu____12262 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12386 =
                            let uu____12393 = as_deferred probs.wl_deferred
                               in
                            let uu____12394 =
                              as_deferred probs.wl_deferred_to_tac  in
                            (uu____12393, uu____12394, (probs.wl_implicits))
                             in
                          Success uu____12386
                      | uu____12395 ->
                          let uu____12405 =
                            let uu___1717_12406 = probs  in
                            let uu____12407 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12428  ->
                                      match uu____12428 with
                                      | (uu____12436,uu____12437,y) -> y))
                               in
                            {
                              attempting = uu____12407;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1717_12406.wl_deferred_to_tac);
                              ctr = (uu___1717_12406.ctr);
                              defer_ok = (uu___1717_12406.defer_ok);
                              smt_ok = (uu___1717_12406.smt_ok);
                              umax_heuristic_ok =
                                (uu___1717_12406.umax_heuristic_ok);
                              tcenv = (uu___1717_12406.tcenv);
                              wl_implicits = (uu___1717_12406.wl_implicits)
                            }  in
                          solve env uu____12405))))

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
            let uu____12446 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12446 with
            | USolved wl1 ->
                let uu____12448 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12448
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12451 = defer_lit "" orig wl1  in
                solve env uu____12451

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
                  let uu____12502 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12502 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12505 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12518;
                  FStar_Syntax_Syntax.vars = uu____12519;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12522;
                  FStar_Syntax_Syntax.vars = uu____12523;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12536,uu____12537) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12545,FStar_Syntax_Syntax.Tm_uinst uu____12546) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12554 -> USolved wl

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
            ((let uu____12565 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12565
              then
                let uu____12570 = prob_to_string env orig  in
                let uu____12572 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12570 uu____12572
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
            let uu___1799_12587 = wl1  in
            let uu____12588 =
              let uu____12598 =
                let uu____12606 = FStar_Thunk.mkv reason  in
                ((wl1.ctr), uu____12606, orig)  in
              uu____12598 :: (wl1.wl_deferred_to_tac)  in
            {
              attempting = (uu___1799_12587.attempting);
              wl_deferred = (uu___1799_12587.wl_deferred);
              wl_deferred_to_tac = uu____12588;
              ctr = (uu___1799_12587.ctr);
              defer_ok = (uu___1799_12587.defer_ok);
              smt_ok = (uu___1799_12587.smt_ok);
              umax_heuristic_ok = (uu___1799_12587.umax_heuristic_ok);
              tcenv = (uu___1799_12587.tcenv);
              wl_implicits = (uu___1799_12587.wl_implicits)
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
                let uu____12635 = FStar_Syntax_Util.head_and_args t  in
                match uu____12635 with
                | (head1,uu____12659) ->
                    let uu____12684 =
                      let uu____12685 = FStar_Syntax_Subst.compress head1  in
                      uu____12685.FStar_Syntax_Syntax.n  in
                    (match uu____12684 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12695) ->
                         let uu____12712 =
                           should_defer_uvar_to_user_tac wl.tcenv uv  in
                         (uu____12712,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12716 -> (false, ""))
                 in
              let uu____12721 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs  in
              (match uu____12721 with
               | (l1,r1) ->
                   let uu____12734 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs  in
                   (match uu____12734 with
                    | (l2,r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12751 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl
                              in
                           solve env uu____12751)))
          | uu____12752 ->
              let uu____12753 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl  in
              solve env uu____12753

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
               let uu____12839 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12839 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12894 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12894
                then
                  let uu____12899 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12901 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12899 uu____12901
                else ());
               (let uu____12906 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12906 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12952 = eq_prob t1 t2 wl2  in
                         (match uu____12952 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12973 ->
                         let uu____12982 = eq_prob t1 t2 wl2  in
                         (match uu____12982 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13032 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13047 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13048 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13047, uu____13048)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13053 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13054 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13053, uu____13054)
                            in
                         (match uu____13032 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13085 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13085 with
                                | (t1_hd,t1_args) ->
                                    let uu____13130 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13130 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13196 =
                                              let uu____13203 =
                                                let uu____13214 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____13214 :: t1_args  in
                                              let uu____13231 =
                                                let uu____13240 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____13240 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____13289  ->
                                                   fun uu____13290  ->
                                                     fun uu____13291  ->
                                                       match (uu____13289,
                                                               uu____13290,
                                                               uu____13291)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____13341),
                                                          (a2,uu____13343))
                                                           ->
                                                           let uu____13380 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13380
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13203
                                                uu____13231
                                               in
                                            match uu____13196 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1902_13406 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1902_13406.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1902_13406.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1902_13406.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1902_13406.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13417 =
                                                  solve env1 wl'  in
                                                (match uu____13417 with
                                                 | Success
                                                     (uu____13420,defer_to_tac,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13424 =
                                                         extend_wl wl4
                                                           defer_to_tac imps
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13424))
                                                 | Failed uu____13425 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13457 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13457 with
                                | (t1_base,p1_opt) ->
                                    let uu____13493 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13493 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13592 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13592
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
                                               let uu____13645 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13645
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
                                               let uu____13677 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13677
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
                                               let uu____13709 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13709
                                           | uu____13712 -> t_base  in
                                         let uu____13729 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13729 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13743 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13743, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13750 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13750 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13786 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13786 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13822 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13822
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
                              let uu____13846 = combine t11 t21 wl2  in
                              (match uu____13846 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13879 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13879
                                     then
                                       let uu____13884 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13884
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13926 ts1 =
               match uu____13926 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13989 = pairwise out t wl2  in
                        (match uu____13989 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14025 =
               let uu____14036 = FStar_List.hd ts  in (uu____14036, [], wl1)
                in
             let uu____14045 = FStar_List.tl ts  in
             aux uu____14025 uu____14045  in
           let uu____14052 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14052 with
           | (this_flex,this_rigid) ->
               let uu____14078 =
                 let uu____14079 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14079.FStar_Syntax_Syntax.n  in
               (match uu____14078 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14104 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14104
                    then
                      let uu____14107 = destruct_flex_t this_flex wl  in
                      (match uu____14107 with
                       | (flex,wl1) ->
                           let uu____14114 = quasi_pattern env flex  in
                           (match uu____14114 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____14133 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14133
                                  then
                                    let uu____14138 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14138
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14145 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2012_14148 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2012_14148.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2012_14148.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2012_14148.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2012_14148.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2012_14148.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2012_14148.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2012_14148.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2012_14148.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2012_14148.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14145)
                | uu____14149 ->
                    ((let uu____14151 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14151
                      then
                        let uu____14156 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14156
                      else ());
                     (let uu____14161 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14161 with
                      | (u,_args) ->
                          let uu____14204 =
                            let uu____14205 = FStar_Syntax_Subst.compress u
                               in
                            uu____14205.FStar_Syntax_Syntax.n  in
                          (match uu____14204 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____14233 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____14233 with
                                 | (u',uu____14252) ->
                                     let uu____14277 =
                                       let uu____14278 = whnf env u'  in
                                       uu____14278.FStar_Syntax_Syntax.n  in
                                     (match uu____14277 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14300 -> false)
                                  in
                               let uu____14302 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_14325  ->
                                         match uu___26_14325 with
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
                                              | uu____14339 -> false)
                                         | uu____14343 -> false))
                                  in
                               (match uu____14302 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14358 = whnf env this_rigid
                                         in
                                      let uu____14359 =
                                        FStar_List.collect
                                          (fun uu___27_14365  ->
                                             match uu___27_14365 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14371 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14371]
                                             | uu____14375 -> [])
                                          bounds_probs
                                         in
                                      uu____14358 :: uu____14359  in
                                    let uu____14376 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14376 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14409 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14424 =
                                               let uu____14425 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14425.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14424 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14437 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14437)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14448 -> bound  in
                                           let uu____14449 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14449)  in
                                         (match uu____14409 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14484 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14484
                                                then
                                                  let wl'1 =
                                                    let uu___2072_14490 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2072_14490.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2072_14490.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2072_14490.ctr);
                                                      defer_ok =
                                                        (uu___2072_14490.defer_ok);
                                                      smt_ok =
                                                        (uu___2072_14490.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2072_14490.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2072_14490.tcenv);
                                                      wl_implicits =
                                                        (uu___2072_14490.wl_implicits)
                                                    }  in
                                                  let uu____14491 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14491
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14497 =
                                                  solve_t env eq_prob
                                                    (let uu___2077_14499 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2077_14499.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2077_14499.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2077_14499.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2077_14499.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2077_14499.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2077_14499.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____14497 with
                                                | Success
                                                    (uu____14501,defer_to_tac,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2084_14505 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2084_14505.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2084_14505.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2084_14505.ctr);
                                                        defer_ok =
                                                          (uu___2084_14505.defer_ok);
                                                        smt_ok =
                                                          (uu___2084_14505.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2084_14505.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2084_14505.tcenv);
                                                        wl_implicits =
                                                          (uu___2084_14505.wl_implicits)
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
                                                    let uu____14522 =
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
                                                    ((let uu____14534 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14534
                                                      then
                                                        let uu____14539 =
                                                          let uu____14541 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14541
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14539
                                                      else ());
                                                     (let uu____14554 =
                                                        let uu____14569 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14569)
                                                         in
                                                      match uu____14554 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14591))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14617 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14617
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
                                                                  let uu____14637
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14637))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14662 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14662
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
                                                                    let uu____14682
                                                                    =
                                                                    let uu____14687
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14687
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14682
                                                                    [] wl2
                                                                     in
                                                                  let uu____14693
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14693))))
                                                      | uu____14694 ->
                                                          let uu____14709 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14709 p)))))))
                           | uu____14716 when flip ->
                               let uu____14717 =
                                 let uu____14719 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14721 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14719 uu____14721
                                  in
                               failwith uu____14717
                           | uu____14724 ->
                               let uu____14725 =
                                 let uu____14727 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14729 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14727 uu____14729
                                  in
                               failwith uu____14725)))))

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
                      (fun uu____14765  ->
                         match uu____14765 with
                         | (x,i) ->
                             let uu____14784 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14784, i)) bs_lhs
                     in
                  let uu____14787 = lhs  in
                  match uu____14787 with
                  | Flex (uu____14788,u_lhs,uu____14790) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14887 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14897 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14897, univ)
                             in
                          match uu____14887 with
                          | (k,univ) ->
                              let uu____14904 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14904 with
                               | (uu____14921,u,wl3) ->
                                   let uu____14924 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14924, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14950 =
                              let uu____14963 =
                                let uu____14974 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14974 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15025  ->
                                   fun uu____15026  ->
                                     match (uu____15025, uu____15026) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15127 =
                                           let uu____15134 =
                                             let uu____15137 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15137
                                              in
                                           copy_uvar u_lhs [] uu____15134 wl2
                                            in
                                         (match uu____15127 with
                                          | (uu____15166,t_a,wl3) ->
                                              let uu____15169 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____15169 with
                                               | (uu____15188,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14963
                                ([], wl1)
                               in
                            (match uu____14950 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2197_15244 = ct  in
                                   let uu____15245 =
                                     let uu____15248 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____15248
                                      in
                                   let uu____15263 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2197_15244.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2197_15244.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15245;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15263;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2197_15244.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2200_15281 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2200_15281.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2200_15281.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____15284 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____15284 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15322 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____15322 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15333 =
                                          let uu____15338 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15338)  in
                                        TERM uu____15333  in
                                      let uu____15339 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15339 with
                                       | (sub_prob,wl3) ->
                                           let uu____15353 =
                                             let uu____15354 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15354
                                              in
                                           solve env uu____15353))
                             | (x,imp)::formals2 ->
                                 let uu____15376 =
                                   let uu____15383 =
                                     let uu____15386 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15386
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15383 wl1
                                    in
                                 (match uu____15376 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15407 =
                                          let uu____15410 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15410
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15407 u_x
                                         in
                                      let uu____15411 =
                                        let uu____15414 =
                                          let uu____15417 =
                                            let uu____15418 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15418, imp)  in
                                          [uu____15417]  in
                                        FStar_List.append bs_terms
                                          uu____15414
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15411 formals2 wl2)
                              in
                           let uu____15445 = occurs_check u_lhs arrow1  in
                           (match uu____15445 with
                            | (uu____15458,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15474 =
                                    FStar_Thunk.mk
                                      (fun uu____15478  ->
                                         let uu____15479 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15479)
                                     in
                                  giveup_or_defer env orig wl uu____15474
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
              (let uu____15512 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15512
               then
                 let uu____15517 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15520 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15517 (rel_to_string (p_rel orig)) uu____15520
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15651 = rhs wl1 scope env1 subst1  in
                     (match uu____15651 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15674 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15674
                            then
                              let uu____15679 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15679
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15757 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15757 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2270_15759 = hd1  in
                       let uu____15760 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2270_15759.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2270_15759.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15760
                       }  in
                     let hd21 =
                       let uu___2273_15764 = hd2  in
                       let uu____15765 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2273_15764.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2273_15764.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15765
                       }  in
                     let uu____15768 =
                       let uu____15773 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15773
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15768 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15796 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15796
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15803 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15803 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15875 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15875
                                  in
                               ((let uu____15893 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15893
                                 then
                                   let uu____15898 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15900 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15898
                                     uu____15900
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15935 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15971 = aux wl [] env [] bs1 bs2  in
               match uu____15971 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16030 = attempt sub_probs wl2  in
                   solve env1 uu____16030)

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
            let uu___2311_16050 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2311_16050.wl_deferred_to_tac);
              ctr = (uu___2311_16050.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2311_16050.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16062 = try_solve env wl'  in
          match uu____16062 with
          | Success (uu____16063,defer_to_tac,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps  in solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16076 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16076 wl)

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
            let uu____16082 = should_defer_flex_to_user_tac wl lhs  in
            if uu____16082
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16095 =
                   FStar_List.map FStar_Pervasives_Native.fst bs  in
                 FStar_Util.as_set uu____16095 FStar_Syntax_Syntax.order_bv
                  in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16129 = lhs1  in
                 match uu____16129 with
                 | Flex (uu____16132,ctx_u,uu____16134) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16142 ->
                           let uu____16143 = sn_binders env1 bs  in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16143 rhs1
                        in
                     [TERM (ctx_u, sol)]
                  in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16192 = quasi_pattern env1 lhs1  in
                 match uu____16192 with
                 | FStar_Pervasives_Native.None  ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs,uu____16226) ->
                     let uu____16231 = lhs1  in
                     (match uu____16231 with
                      | Flex (t_lhs,ctx_u,args) ->
                          let uu____16246 = occurs_check ctx_u rhs1  in
                          (match uu____16246 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16297 =
                                   let uu____16305 =
                                     let uu____16307 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16307
                                      in
                                   FStar_Util.Inl uu____16305  in
                                 (uu____16297, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs)
                                     in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1
                                     in
                                  let uu____16335 =
                                    let uu____16337 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs
                                       in
                                    Prims.op_Negation uu____16337  in
                                  if uu____16335
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16364 =
                                       let uu____16372 =
                                         mk_solution env1 lhs1 bs rhs1  in
                                       FStar_Util.Inr uu____16372  in
                                     let uu____16378 =
                                       restrict_all_uvars ctx_u uvars1 wl1
                                        in
                                     (uu____16364, uu____16378)))))
                  in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16422 = FStar_Syntax_Util.head_and_args rhs1  in
                 match uu____16422 with
                 | (rhs_hd,args) ->
                     let uu____16465 = FStar_Util.prefix args  in
                     (match uu____16465 with
                      | (args_rhs,last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              FStar_Pervasives_Native.None
                              rhs1.FStar_Syntax_Syntax.pos
                             in
                          let uu____16537 = lhs1  in
                          (match uu____16537 with
                           | Flex (t_lhs,u_lhs,_lhs_args) ->
                               let uu____16541 =
                                 let uu____16552 =
                                   let uu____16559 =
                                     let uu____16562 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16562
                                      in
                                   copy_uvar u_lhs [] uu____16559 wl1  in
                                 match uu____16552 with
                                 | (uu____16589,t_last_arg,wl2) ->
                                     let uu____16592 =
                                       let uu____16599 =
                                         let uu____16600 =
                                           let uu____16609 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg
                                              in
                                           [uu____16609]  in
                                         FStar_List.append bs_lhs uu____16600
                                          in
                                       copy_uvar u_lhs uu____16599 t_res_lhs
                                         wl2
                                        in
                                     (match uu____16592 with
                                      | (uu____16644,lhs',wl3) ->
                                          let uu____16647 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3
                                             in
                                          (match uu____16647 with
                                           | (uu____16664,lhs'_last_arg,wl4)
                                               -> (lhs', lhs'_last_arg, wl4)))
                                  in
                               (match uu____16541 with
                                | (lhs',lhs'_last_arg,wl2) ->
                                    let sol =
                                      let uu____16685 =
                                        let uu____16686 =
                                          let uu____16691 =
                                            let uu____16692 =
                                              let uu____16695 =
                                                let uu____16700 =
                                                  let uu____16701 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      lhs'_last_arg
                                                     in
                                                  [uu____16701]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  lhs' uu____16700
                                                 in
                                              uu____16695
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16692
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16691)  in
                                        TERM uu____16686  in
                                      [uu____16685]  in
                                    let uu____16726 =
                                      let uu____16733 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs"
                                         in
                                      match uu____16733 with
                                      | (p1,wl3) ->
                                          let uu____16753 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs"
                                             in
                                          (match uu____16753 with
                                           | (p2,wl4) -> ([p1; p2], wl4))
                                       in
                                    (match uu____16726 with
                                     | (sub_probs,wl3) ->
                                         let uu____16785 =
                                           let uu____16786 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16786  in
                                         solve env1 uu____16785))))
                  in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16820 = FStar_Syntax_Util.head_and_args rhs2  in
                   match uu____16820 with
                   | (uu____16838,args) ->
                       (match args with | [] -> false | uu____16874 -> true)
                    in
                 let is_arrow rhs2 =
                   let uu____16893 =
                     let uu____16894 = FStar_Syntax_Subst.compress rhs2  in
                     uu____16894.FStar_Syntax_Syntax.n  in
                   match uu____16893 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____16898 -> true
                   | uu____16914 -> false  in
                 let uu____16916 = quasi_pattern env1 lhs1  in
                 match uu____16916 with
                 | FStar_Pervasives_Native.None  ->
                     let msg =
                       FStar_Thunk.mk
                         (fun uu____16934  ->
                            let uu____16935 = prob_to_string env1 orig1  in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____16935)
                        in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                     let uu____16944 = is_app rhs1  in
                     if uu____16944
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____16949 = is_arrow rhs1  in
                        if uu____16949
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             FStar_Thunk.mk
                               (fun uu____16961  ->
                                  let uu____16962 = prob_to_string env1 orig1
                                     in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____16962)
                              in
                           giveup_or_defer env1 orig1 wl1 msg))
                  in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB  ->
                   if wl.defer_ok
                   then
                     let uu____16966 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16966
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV  ->
                   if wl.defer_ok
                   then
                     let uu____16972 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16972
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ  ->
                   let uu____16977 = lhs  in
                   (match uu____16977 with
                    | Flex (_t1,ctx_uv,args_lhs) ->
                        let uu____16981 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs
                           in
                        (match uu____16981 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs  in
                             let names_to_string1 fvs =
                               let uu____16999 =
                                 let uu____17003 =
                                   FStar_Util.set_elements fvs  in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____17003
                                  in
                               FStar_All.pipe_right uu____16999
                                 (FStar_String.concat ", ")
                                in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders)
                                in
                             let fvs2 = FStar_Syntax_Free.names rhs1  in
                             let uu____17024 = occurs_check ctx_uv rhs1  in
                             (match uu____17024 with
                              | (uvars1,occurs_ok,msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17053 =
                                      let uu____17054 =
                                        let uu____17056 =
                                          FStar_Option.get msg  in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17056
                                         in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17054
                                       in
                                    giveup_or_defer env orig wl uu____17053
                                  else
                                    (let uu____17064 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1
                                        in
                                     if uu____17064
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1
                                          in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars1 wl
                                          in
                                       let uu____17071 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1
                                          in
                                       solve env uu____17071
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            FStar_Thunk.mk
                                              (fun uu____17084  ->
                                                 let uu____17085 =
                                                   names_to_string1 fvs2  in
                                                 let uu____17087 =
                                                   names_to_string1 fvs1  in
                                                 let uu____17089 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders)
                                                    in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17085 uu____17087
                                                   uu____17089)
                                             in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17101 ->
                             if wl.defer_ok
                             then
                               let uu____17105 =
                                 FStar_Thunk.mkv "Not a pattern"  in
                               giveup_or_defer env orig wl uu____17105
                             else
                               (let uu____17110 =
                                  try_quasi_pattern orig env wl lhs rhs  in
                                match uu____17110 with
                                | (FStar_Util.Inr sol,wl1) ->
                                    let uu____17136 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17136
                                | (FStar_Util.Inl msg,uu____17138) ->
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
                  let uu____17156 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17156
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____17162 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17162
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17167 =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs)
                   in
                if uu____17167
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
                    (let uu____17174 =
                       FStar_Thunk.mkv "flex-flex non-pattern"  in
                     giveup_or_defer env orig wl uu____17174)
                  else
                    (let uu____17179 =
                       let uu____17196 = quasi_pattern env lhs  in
                       let uu____17203 = quasi_pattern env rhs  in
                       (uu____17196, uu____17203)  in
                     match uu____17179 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                        (binders_rhs,t_res_rhs)) ->
                         let uu____17246 = lhs  in
                         (match uu____17246 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17247;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17249;_},u_lhs,uu____17251)
                              ->
                              let uu____17254 = rhs  in
                              (match uu____17254 with
                               | Flex (uu____17255,u_rhs,uu____17257) ->
                                   let uu____17258 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs)
                                      in
                                   if uu____17258
                                   then
                                     let uu____17265 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl
                                        in
                                     solve env uu____17265
                                   else
                                     (let uu____17268 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      match uu____17268 with
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
                                          let uu____17300 =
                                            let uu____17307 =
                                              let uu____17310 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs
                                                 in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17310
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
                                              uu____17307
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None
                                             in
                                          (match uu____17300 with
                                           | (uu____17316,w,wl1) ->
                                               let w_app =
                                                 let uu____17322 =
                                                   let uu____17327 =
                                                     FStar_List.map
                                                       (fun uu____17338  ->
                                                          match uu____17338
                                                          with
                                                          | (z,uu____17346)
                                                              ->
                                                              let uu____17351
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  z
                                                                 in
                                                              FStar_Syntax_Syntax.as_arg
                                                                uu____17351)
                                                       zs
                                                      in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     w uu____17327
                                                    in
                                                 uu____17322
                                                   FStar_Pervasives_Native.None
                                                   w.FStar_Syntax_Syntax.pos
                                                  in
                                               ((let uu____17353 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17353
                                                 then
                                                   let uu____17358 =
                                                     let uu____17362 =
                                                       flex_t_to_string lhs
                                                        in
                                                     let uu____17364 =
                                                       let uu____17368 =
                                                         flex_t_to_string rhs
                                                          in
                                                       let uu____17370 =
                                                         let uu____17374 =
                                                           term_to_string w
                                                            in
                                                         let uu____17376 =
                                                           let uu____17380 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs)
                                                              in
                                                           let uu____17389 =
                                                             let uu____17393
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                in
                                                             let uu____17402
                                                               =
                                                               let uu____17406
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs
                                                                  in
                                                               [uu____17406]
                                                                in
                                                             uu____17393 ::
                                                               uu____17402
                                                              in
                                                           uu____17380 ::
                                                             uu____17389
                                                            in
                                                         uu____17374 ::
                                                           uu____17376
                                                          in
                                                       uu____17368 ::
                                                         uu____17370
                                                        in
                                                     uu____17362 ::
                                                       uu____17364
                                                      in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17358
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17423 =
                                                       let uu____17428 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs))
                                                          in
                                                       (u_lhs, uu____17428)
                                                        in
                                                     TERM uu____17423  in
                                                   let uu____17429 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                      in
                                                   if uu____17429
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17437 =
                                                          let uu____17442 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_rhs,
                                                            uu____17442)
                                                           in
                                                        TERM uu____17437  in
                                                      [s1; s2])
                                                    in
                                                 let uu____17443 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1
                                                    in
                                                 solve env uu____17443))))))
                     | uu____17444 ->
                         let uu____17461 =
                           FStar_Thunk.mkv "flex-flex: non-patterns"  in
                         giveup_or_defer env orig wl uu____17461)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17515 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17515
            then
              let uu____17520 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17522 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17524 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17526 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17520 uu____17522 uu____17524 uu____17526
            else ());
           (let uu____17537 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17537 with
            | (head1,args1) ->
                let uu____17580 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17580 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17650 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17650 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17655 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17655)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17676 =
                         FStar_Thunk.mk
                           (fun uu____17683  ->
                              let uu____17684 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17686 = args_to_string args1  in
                              let uu____17690 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17692 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17684 uu____17686 uu____17690
                                uu____17692)
                          in
                       giveup env1 uu____17676 orig
                     else
                       (let uu____17699 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17704 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17704 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17699
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2583_17708 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2583_17708.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2583_17708.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2583_17708.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2583_17708.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2583_17708.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2583_17708.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2583_17708.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2583_17708.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17718 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17718
                                    else solve env1 wl2))
                        else
                          (let uu____17723 = base_and_refinement env1 t1  in
                           match uu____17723 with
                           | (base1,refinement1) ->
                               let uu____17748 = base_and_refinement env1 t2
                                  in
                               (match uu____17748 with
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
                                           let uu____17913 =
                                             FStar_List.fold_right
                                               (fun uu____17953  ->
                                                  fun uu____17954  ->
                                                    match (uu____17953,
                                                            uu____17954)
                                                    with
                                                    | (((a1,uu____18006),
                                                        (a2,uu____18008)),
                                                       (probs,wl3)) ->
                                                        let uu____18057 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18057
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17913 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18100 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18100
                                                 then
                                                   let uu____18105 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18105
                                                 else ());
                                                (let uu____18111 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18111
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
                                                    (let uu____18138 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18138 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18154 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18154
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18162 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18162))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18187 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18187 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18203 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18203
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18211 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18211)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18239 =
                                           match uu____18239 with
                                           | (prob,reason) ->
                                               ((let uu____18256 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18256
                                                 then
                                                   let uu____18261 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18263 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____18265 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____18261 uu____18263
                                                     uu____18265
                                                 else ());
                                                (let uu____18271 =
                                                   let uu____18280 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18283 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18280, uu____18283)
                                                    in
                                                 match uu____18271 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18296 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18296 with
                                                      | (head1',uu____18314)
                                                          ->
                                                          let uu____18339 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18339
                                                           with
                                                           | (head2',uu____18357)
                                                               ->
                                                               let uu____18382
                                                                 =
                                                                 let uu____18387
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18388
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18387,
                                                                   uu____18388)
                                                                  in
                                                               (match uu____18382
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18390
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18390
                                                                    then
                                                                    let uu____18395
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18397
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18399
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18401
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18395
                                                                    uu____18397
                                                                    uu____18399
                                                                    uu____18401
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18406
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2671_18414
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2671_18414.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2671_18414.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2671_18414.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2671_18414.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2671_18414.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2671_18414.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2671_18414.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2671_18414.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18416
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18416
                                                                    then
                                                                    let uu____18421
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18421
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18426 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18438 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18438 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18446 =
                                             let uu____18447 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18447.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18446 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18452 -> false  in
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
                                          | uu____18455 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18458 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2691_18494 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2691_18494.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2691_18494.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2691_18494.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2691_18494.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2691_18494.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2691_18494.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2691_18494.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2691_18494.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18570 = destruct_flex_t scrutinee wl1  in
             match uu____18570 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____18581 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18581 with
                  | (xs,pat_term,uu____18597,uu____18598) ->
                      let uu____18603 =
                        FStar_List.fold_left
                          (fun uu____18626  ->
                             fun x  ->
                               match uu____18626 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18647 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18647 with
                                    | (uu____18666,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18603 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18687 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18687 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2732_18704 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2732_18704.wl_deferred_to_tac);
                                    ctr = (uu___2732_18704.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2732_18704.umax_heuristic_ok);
                                    tcenv = (uu___2732_18704.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18715 = solve env1 wl'  in
                                (match uu____18715 with
                                 | Success (uu____18718,defer_to_tac,imps) ->
                                     let wl'1 =
                                       let uu___2741_18722 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2741_18722.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2741_18722.wl_deferred_to_tac);
                                         ctr = (uu___2741_18722.ctr);
                                         defer_ok =
                                           (uu___2741_18722.defer_ok);
                                         smt_ok = (uu___2741_18722.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2741_18722.umax_heuristic_ok);
                                         tcenv = (uu___2741_18722.tcenv);
                                         wl_implicits =
                                           (uu___2741_18722.wl_implicits)
                                       }  in
                                     let uu____18723 = solve env1 wl'1  in
                                     (match uu____18723 with
                                      | Success
                                          (uu____18726,defer_to_tac',imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18730 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps')
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____18730))
                                      | Failed uu____18736 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18742 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18765 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18765
                 then
                   let uu____18770 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18772 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18770 uu____18772
                 else ());
                (let uu____18777 =
                   let uu____18798 =
                     let uu____18807 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18807)  in
                   let uu____18814 =
                     let uu____18823 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18823)  in
                   (uu____18798, uu____18814)  in
                 match uu____18777 with
                 | ((uu____18853,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18856;
                                   FStar_Syntax_Syntax.vars = uu____18857;_}),
                    (s,t)) ->
                     let uu____18928 =
                       let uu____18930 = is_flex scrutinee  in
                       Prims.op_Negation uu____18930  in
                     if uu____18928
                     then
                       ((let uu____18941 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18941
                         then
                           let uu____18946 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18946
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18965 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18965
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18980 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18980
                           then
                             let uu____18985 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18987 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18985 uu____18987
                           else ());
                          (let pat_discriminates uu___28_19012 =
                             match uu___28_19012 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19028;
                                  FStar_Syntax_Syntax.p = uu____19029;_},FStar_Pervasives_Native.None
                                ,uu____19030) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19044;
                                  FStar_Syntax_Syntax.p = uu____19045;_},FStar_Pervasives_Native.None
                                ,uu____19046) -> true
                             | uu____19073 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19176 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19176 with
                                       | (uu____19178,uu____19179,t') ->
                                           let uu____19197 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19197 with
                                            | (FullMatch ,uu____19209) ->
                                                true
                                            | (HeadMatch
                                               uu____19223,uu____19224) ->
                                                true
                                            | uu____19239 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19276 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19276
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19287 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19287 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19375,uu____19376) ->
                                       branches1
                                   | uu____19521 -> branches  in
                                 let uu____19576 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19585 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19585 with
                                        | (p,uu____19589,uu____19590) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19619  -> FStar_Util.Inr _19619)
                                   uu____19576))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19649 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19649 with
                                | (p,uu____19658,e) ->
                                    ((let uu____19677 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19677
                                      then
                                        let uu____19682 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19684 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19682 uu____19684
                                      else ());
                                     (let uu____19689 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19704  -> FStar_Util.Inr _19704)
                                        uu____19689)))))
                 | ((s,t),(uu____19707,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19710;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19711;_}))
                     ->
                     let uu____19780 =
                       let uu____19782 = is_flex scrutinee  in
                       Prims.op_Negation uu____19782  in
                     if uu____19780
                     then
                       ((let uu____19793 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19793
                         then
                           let uu____19798 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19798
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19817 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19817
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19832 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19832
                           then
                             let uu____19837 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19839 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19837 uu____19839
                           else ());
                          (let pat_discriminates uu___28_19864 =
                             match uu___28_19864 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19880;
                                  FStar_Syntax_Syntax.p = uu____19881;_},FStar_Pervasives_Native.None
                                ,uu____19882) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19896;
                                  FStar_Syntax_Syntax.p = uu____19897;_},FStar_Pervasives_Native.None
                                ,uu____19898) -> true
                             | uu____19925 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20028 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20028 with
                                       | (uu____20030,uu____20031,t') ->
                                           let uu____20049 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20049 with
                                            | (FullMatch ,uu____20061) ->
                                                true
                                            | (HeadMatch
                                               uu____20075,uu____20076) ->
                                                true
                                            | uu____20091 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20128 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20128
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20139 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20139 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20227,uu____20228) ->
                                       branches1
                                   | uu____20373 -> branches  in
                                 let uu____20428 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20437 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20437 with
                                        | (p,uu____20441,uu____20442) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _20471  -> FStar_Util.Inr _20471)
                                   uu____20428))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20501 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20501 with
                                | (p,uu____20510,e) ->
                                    ((let uu____20529 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20529
                                      then
                                        let uu____20534 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20536 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20534 uu____20536
                                      else ());
                                     (let uu____20541 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _20556  -> FStar_Util.Inr _20556)
                                        uu____20541)))))
                 | uu____20557 ->
                     ((let uu____20579 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20579
                       then
                         let uu____20584 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20586 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20584 uu____20586
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20632 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20632
            then
              let uu____20637 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20639 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20641 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20643 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20637 uu____20639 uu____20641 uu____20643
            else ());
           (let uu____20648 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20648 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20679,uu____20680) ->
                     let rec may_relate head3 =
                       let uu____20708 =
                         let uu____20709 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20709.FStar_Syntax_Syntax.n  in
                       match uu____20708 with
                       | FStar_Syntax_Syntax.Tm_name uu____20713 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20715 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20740 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20740 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20742 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20745
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20746 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20749,uu____20750) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20792) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20798) ->
                           may_relate t
                       | uu____20803 -> false  in
                     let uu____20805 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20805 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20818 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20818
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20828 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20828
                          then
                            let uu____20831 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20831 with
                             | (guard,wl2) ->
                                 let uu____20838 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20838)
                          else
                            (let uu____20841 =
                               FStar_Thunk.mk
                                 (fun uu____20848  ->
                                    let uu____20849 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20851 =
                                      let uu____20853 =
                                        let uu____20857 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20857
                                          (fun x  ->
                                             let uu____20864 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20864)
                                         in
                                      FStar_Util.dflt "" uu____20853  in
                                    let uu____20869 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20871 =
                                      let uu____20873 =
                                        let uu____20877 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20877
                                          (fun x  ->
                                             let uu____20884 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20884)
                                         in
                                      FStar_Util.dflt "" uu____20873  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20849 uu____20851 uu____20869
                                      uu____20871)
                                in
                             giveup env1 uu____20841 orig))
                 | (HeadMatch (true ),uu____20890) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20905 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20905 with
                        | (guard,wl2) ->
                            let uu____20912 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20912)
                     else
                       (let uu____20915 =
                          FStar_Thunk.mk
                            (fun uu____20920  ->
                               let uu____20921 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20923 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20921 uu____20923)
                           in
                        giveup env1 uu____20915 orig)
                 | (uu____20926,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2923_20940 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2923_20940.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2923_20940.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2923_20940.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2923_20940.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2923_20940.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2923_20940.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2923_20940.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2923_20940.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20967 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20967
          then
            let uu____20970 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20970
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20976 =
                let uu____20979 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20979  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20976 t1);
             (let uu____20998 =
                let uu____21001 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____21001  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20998 t2);
             (let uu____21020 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____21020
              then
                let uu____21024 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____21026 =
                  let uu____21028 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____21030 =
                    let uu____21032 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____21032  in
                  Prims.op_Hat uu____21028 uu____21030  in
                let uu____21035 =
                  let uu____21037 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____21039 =
                    let uu____21041 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____21041  in
                  Prims.op_Hat uu____21037 uu____21039  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21024 uu____21026 uu____21035
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21048,uu____21049) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21065,FStar_Syntax_Syntax.Tm_delayed uu____21066) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21082,uu____21083) ->
                  let uu____21110 =
                    let uu___2954_21111 = problem  in
                    let uu____21112 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2954_21111.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21112;
                      FStar_TypeChecker_Common.relation =
                        (uu___2954_21111.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2954_21111.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2954_21111.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2954_21111.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2954_21111.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2954_21111.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2954_21111.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2954_21111.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21110 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21113,uu____21114) ->
                  let uu____21121 =
                    let uu___2960_21122 = problem  in
                    let uu____21123 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2960_21122.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21123;
                      FStar_TypeChecker_Common.relation =
                        (uu___2960_21122.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2960_21122.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2960_21122.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2960_21122.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2960_21122.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2960_21122.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2960_21122.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2960_21122.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21121 wl
              | (uu____21124,FStar_Syntax_Syntax.Tm_ascribed uu____21125) ->
                  let uu____21152 =
                    let uu___2966_21153 = problem  in
                    let uu____21154 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2966_21153.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2966_21153.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2966_21153.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21154;
                      FStar_TypeChecker_Common.element =
                        (uu___2966_21153.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2966_21153.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2966_21153.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2966_21153.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2966_21153.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2966_21153.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21152 wl
              | (uu____21155,FStar_Syntax_Syntax.Tm_meta uu____21156) ->
                  let uu____21163 =
                    let uu___2972_21164 = problem  in
                    let uu____21165 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2972_21164.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2972_21164.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2972_21164.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21165;
                      FStar_TypeChecker_Common.element =
                        (uu___2972_21164.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2972_21164.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2972_21164.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2972_21164.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2972_21164.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2972_21164.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21163 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21167),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21169)) ->
                  let uu____21178 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21178
              | (FStar_Syntax_Syntax.Tm_bvar uu____21179,uu____21180) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21182,FStar_Syntax_Syntax.Tm_bvar uu____21183) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_21253 =
                    match uu___29_21253 with
                    | [] -> c
                    | bs ->
                        let uu____21281 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21281
                     in
                  let uu____21292 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21292 with
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
                                    let uu____21441 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21441
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
                  let mk_t t l uu___30_21530 =
                    match uu___30_21530 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21572 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21572 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21717 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21718 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21717
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21718 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21720,uu____21721) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21752 -> true
                    | uu____21772 -> false  in
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
                      (let uu____21832 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3074_21840 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3074_21840.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3074_21840.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3074_21840.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3074_21840.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3074_21840.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3074_21840.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3074_21840.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3074_21840.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3074_21840.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3074_21840.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3074_21840.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3074_21840.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3074_21840.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3074_21840.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3074_21840.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3074_21840.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3074_21840.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3074_21840.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3074_21840.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3074_21840.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3074_21840.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3074_21840.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3074_21840.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3074_21840.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3074_21840.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3074_21840.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3074_21840.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3074_21840.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3074_21840.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3074_21840.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3074_21840.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3074_21840.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3074_21840.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3074_21840.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3074_21840.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3074_21840.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3074_21840.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3074_21840.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3074_21840.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3074_21840.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3074_21840.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3074_21840.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3074_21840.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3074_21840.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3074_21840.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____21832 with
                       | (uu____21845,ty,uu____21847) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21856 =
                                 let uu____21857 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21857.FStar_Syntax_Syntax.n  in
                               match uu____21856 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21860 ->
                                   let uu____21867 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21867
                               | uu____21868 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21871 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21871
                             then
                               let uu____21876 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21878 =
                                 let uu____21880 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21880
                                  in
                               let uu____21881 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21876 uu____21878 uu____21881
                             else ());
                            r1))
                     in
                  let uu____21886 =
                    let uu____21903 = maybe_eta t1  in
                    let uu____21910 = maybe_eta t2  in
                    (uu____21903, uu____21910)  in
                  (match uu____21886 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3095_21952 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3095_21952.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3095_21952.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3095_21952.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3095_21952.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3095_21952.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3095_21952.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3095_21952.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3095_21952.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21973 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21973
                       then
                         let uu____21976 = destruct_flex_t not_abs wl  in
                         (match uu____21976 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3112_21993 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3112_21993.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3112_21993.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3112_21993.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3112_21993.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3112_21993.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3112_21993.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3112_21993.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3112_21993.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21996 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21996 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22019 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22019
                       then
                         let uu____22022 = destruct_flex_t not_abs wl  in
                         (match uu____22022 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3112_22039 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3112_22039.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3112_22039.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3112_22039.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3112_22039.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3112_22039.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3112_22039.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3112_22039.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3112_22039.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22042 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22042 orig))
                   | uu____22045 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22063,FStar_Syntax_Syntax.Tm_abs uu____22064) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22095 -> true
                    | uu____22115 -> false  in
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
                      (let uu____22175 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3074_22183 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3074_22183.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3074_22183.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3074_22183.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3074_22183.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3074_22183.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3074_22183.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3074_22183.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3074_22183.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3074_22183.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3074_22183.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3074_22183.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3074_22183.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3074_22183.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3074_22183.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3074_22183.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3074_22183.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3074_22183.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3074_22183.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3074_22183.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3074_22183.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3074_22183.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3074_22183.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3074_22183.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3074_22183.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3074_22183.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3074_22183.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3074_22183.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3074_22183.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3074_22183.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3074_22183.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3074_22183.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3074_22183.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3074_22183.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3074_22183.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3074_22183.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3074_22183.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3074_22183.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3074_22183.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3074_22183.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3074_22183.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3074_22183.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3074_22183.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3074_22183.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3074_22183.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3074_22183.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____22175 with
                       | (uu____22188,ty,uu____22190) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22199 =
                                 let uu____22200 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22200.FStar_Syntax_Syntax.n  in
                               match uu____22199 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22203 ->
                                   let uu____22210 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22210
                               | uu____22211 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22214 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22214
                             then
                               let uu____22219 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22221 =
                                 let uu____22223 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22223
                                  in
                               let uu____22224 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22219 uu____22221 uu____22224
                             else ());
                            r1))
                     in
                  let uu____22229 =
                    let uu____22246 = maybe_eta t1  in
                    let uu____22253 = maybe_eta t2  in
                    (uu____22246, uu____22253)  in
                  (match uu____22229 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3095_22295 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3095_22295.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3095_22295.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3095_22295.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3095_22295.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3095_22295.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3095_22295.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3095_22295.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3095_22295.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22316 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22316
                       then
                         let uu____22319 = destruct_flex_t not_abs wl  in
                         (match uu____22319 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3112_22336 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3112_22336.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3112_22336.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3112_22336.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3112_22336.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3112_22336.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3112_22336.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3112_22336.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3112_22336.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22339 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22339 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22362 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22362
                       then
                         let uu____22365 = destruct_flex_t not_abs wl  in
                         (match uu____22365 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3112_22382 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3112_22382.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3112_22382.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3112_22382.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3112_22382.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3112_22382.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3112_22382.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3112_22382.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3112_22382.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22385 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22385 orig))
                   | uu____22388 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22418 =
                    let uu____22423 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22423 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3135_22451 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3135_22451.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3135_22451.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3137_22453 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3137_22453.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3137_22453.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22454,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3135_22469 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3135_22469.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3135_22469.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3137_22471 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3137_22471.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3137_22471.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22472 -> (x1, x2)  in
                  (match uu____22418 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22491 = as_refinement false env t11  in
                       (match uu____22491 with
                        | (x12,phi11) ->
                            let uu____22499 = as_refinement false env t21  in
                            (match uu____22499 with
                             | (x22,phi21) ->
                                 ((let uu____22508 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22508
                                   then
                                     ((let uu____22513 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22515 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22517 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22513
                                         uu____22515 uu____22517);
                                      (let uu____22520 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22522 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22524 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22520
                                         uu____22522 uu____22524))
                                   else ());
                                  (let uu____22529 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22529 with
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
                                         let uu____22600 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22600
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22612 =
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
                                         (let uu____22625 =
                                            let uu____22628 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22628
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22625
                                            (p_guard base_prob));
                                         (let uu____22647 =
                                            let uu____22650 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22650
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22647
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22669 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22669)
                                          in
                                       let has_uvars =
                                         (let uu____22674 =
                                            let uu____22676 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22676
                                             in
                                          Prims.op_Negation uu____22674) ||
                                           (let uu____22680 =
                                              let uu____22682 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22682
                                               in
                                            Prims.op_Negation uu____22680)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22686 =
                                           let uu____22691 =
                                             let uu____22700 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22700]  in
                                           mk_t_problem wl1 uu____22691 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22686 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22723 =
                                                solve env1
                                                  (let uu___3180_22725 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3180_22725.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3180_22725.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3180_22725.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3180_22725.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3180_22725.tcenv);
                                                     wl_implicits =
                                                       (uu___3180_22725.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22723 with
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
                                                   (uu____22740,defer_to_tac,uu____22742)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22747 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22747
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3196_22756 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3196_22756.attempting);
                                                         wl_deferred =
                                                           (uu___3196_22756.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3196_22756.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3196_22756.defer_ok);
                                                         smt_ok =
                                                           (uu___3196_22756.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3196_22756.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3196_22756.tcenv);
                                                         wl_implicits =
                                                           (uu___3196_22756.wl_implicits)
                                                       }  in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac []
                                                        in
                                                     let uu____22759 =
                                                       attempt [base_prob]
                                                         wl5
                                                        in
                                                     solve env1 uu____22759))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22762,FStar_Syntax_Syntax.Tm_uvar uu____22763) ->
                  let uu____22788 = destruct_flex_t t1 wl  in
                  (match uu____22788 with
                   | (f1,wl1) ->
                       let uu____22795 = destruct_flex_t t2 wl1  in
                       (match uu____22795 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22802;
                    FStar_Syntax_Syntax.pos = uu____22803;
                    FStar_Syntax_Syntax.vars = uu____22804;_},uu____22805),FStar_Syntax_Syntax.Tm_uvar
                 uu____22806) ->
                  let uu____22855 = destruct_flex_t t1 wl  in
                  (match uu____22855 with
                   | (f1,wl1) ->
                       let uu____22862 = destruct_flex_t t2 wl1  in
                       (match uu____22862 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22869,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22870;
                    FStar_Syntax_Syntax.pos = uu____22871;
                    FStar_Syntax_Syntax.vars = uu____22872;_},uu____22873))
                  ->
                  let uu____22922 = destruct_flex_t t1 wl  in
                  (match uu____22922 with
                   | (f1,wl1) ->
                       let uu____22929 = destruct_flex_t t2 wl1  in
                       (match uu____22929 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22936;
                    FStar_Syntax_Syntax.pos = uu____22937;
                    FStar_Syntax_Syntax.vars = uu____22938;_},uu____22939),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22940;
                    FStar_Syntax_Syntax.pos = uu____22941;
                    FStar_Syntax_Syntax.vars = uu____22942;_},uu____22943))
                  ->
                  let uu____23016 = destruct_flex_t t1 wl  in
                  (match uu____23016 with
                   | (f1,wl1) ->
                       let uu____23023 = destruct_flex_t t2 wl1  in
                       (match uu____23023 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23030,uu____23031) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23044 = destruct_flex_t t1 wl  in
                  (match uu____23044 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23051;
                    FStar_Syntax_Syntax.pos = uu____23052;
                    FStar_Syntax_Syntax.vars = uu____23053;_},uu____23054),uu____23055)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23092 = destruct_flex_t t1 wl  in
                  (match uu____23092 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23099,FStar_Syntax_Syntax.Tm_uvar uu____23100) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23113,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23114;
                    FStar_Syntax_Syntax.pos = uu____23115;
                    FStar_Syntax_Syntax.vars = uu____23116;_},uu____23117))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23154,FStar_Syntax_Syntax.Tm_arrow uu____23155) ->
                  solve_t' env
                    (let uu___3297_23183 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3297_23183.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3297_23183.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3297_23183.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3297_23183.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3297_23183.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3297_23183.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3297_23183.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3297_23183.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3297_23183.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23184;
                    FStar_Syntax_Syntax.pos = uu____23185;
                    FStar_Syntax_Syntax.vars = uu____23186;_},uu____23187),FStar_Syntax_Syntax.Tm_arrow
                 uu____23188) ->
                  solve_t' env
                    (let uu___3297_23240 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3297_23240.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3297_23240.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3297_23240.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3297_23240.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3297_23240.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3297_23240.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3297_23240.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3297_23240.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3297_23240.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23241,FStar_Syntax_Syntax.Tm_uvar uu____23242) ->
                  let uu____23255 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23255
              | (uu____23256,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23257;
                    FStar_Syntax_Syntax.pos = uu____23258;
                    FStar_Syntax_Syntax.vars = uu____23259;_},uu____23260))
                  ->
                  let uu____23297 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23297
              | (FStar_Syntax_Syntax.Tm_uvar uu____23298,uu____23299) ->
                  let uu____23312 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23312
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23313;
                    FStar_Syntax_Syntax.pos = uu____23314;
                    FStar_Syntax_Syntax.vars = uu____23315;_},uu____23316),uu____23317)
                  ->
                  let uu____23354 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23354
              | (FStar_Syntax_Syntax.Tm_refine uu____23355,uu____23356) ->
                  let t21 =
                    let uu____23364 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23364  in
                  solve_t env
                    (let uu___3332_23390 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3332_23390.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3332_23390.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3332_23390.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3332_23390.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3332_23390.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3332_23390.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3332_23390.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3332_23390.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3332_23390.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23391,FStar_Syntax_Syntax.Tm_refine uu____23392) ->
                  let t11 =
                    let uu____23400 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23400  in
                  solve_t env
                    (let uu___3339_23426 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3339_23426.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3339_23426.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3339_23426.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3339_23426.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3339_23426.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3339_23426.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3339_23426.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3339_23426.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3339_23426.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23508 =
                    let uu____23509 = guard_of_prob env wl problem t1 t2  in
                    match uu____23509 with
                    | (guard,wl1) ->
                        let uu____23516 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23516
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23735 = br1  in
                        (match uu____23735 with
                         | (p1,w1,uu____23764) ->
                             let uu____23781 = br2  in
                             (match uu____23781 with
                              | (p2,w2,uu____23804) ->
                                  let uu____23809 =
                                    let uu____23811 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23811  in
                                  if uu____23809
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23838 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23838 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23875 = br2  in
                                         (match uu____23875 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23908 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23908
                                                 in
                                              let uu____23913 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23944,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23965) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____24024 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____24024 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23913
                                                (fun uu____24096  ->
                                                   match uu____24096 with
                                                   | (wprobs,wl2) ->
                                                       let uu____24133 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____24133
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24154
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24154
                                                              then
                                                                let uu____24159
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24161
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24159
                                                                  uu____24161
                                                              else ());
                                                             (let uu____24167
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24167
                                                                (fun
                                                                   uu____24203
                                                                    ->
                                                                   match uu____24203
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
                    | uu____24332 -> FStar_Pervasives_Native.None  in
                  let uu____24373 = solve_branches wl brs1 brs2  in
                  (match uu____24373 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24399 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24399 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24426 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24426 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24460 =
                                FStar_List.map
                                  (fun uu____24472  ->
                                     match uu____24472 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24460  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24481 =
                              let uu____24482 =
                                let uu____24483 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24483
                                  (let uu___3438_24491 = wl3  in
                                   {
                                     attempting =
                                       (uu___3438_24491.attempting);
                                     wl_deferred =
                                       (uu___3438_24491.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3438_24491.wl_deferred_to_tac);
                                     ctr = (uu___3438_24491.ctr);
                                     defer_ok = (uu___3438_24491.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3438_24491.umax_heuristic_ok);
                                     tcenv = (uu___3438_24491.tcenv);
                                     wl_implicits =
                                       (uu___3438_24491.wl_implicits)
                                   })
                                 in
                              solve env uu____24482  in
                            (match uu____24481 with
                             | Success (ds,ds',imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24497 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24506 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24506 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24509,uu____24510) ->
                  let head1 =
                    let uu____24534 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24534
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24580 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24580
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24626 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24626
                    then
                      let uu____24630 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24632 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24634 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24630 uu____24632 uu____24634
                    else ());
                   (let no_free_uvars t =
                      (let uu____24648 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24648) &&
                        (let uu____24652 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24652)
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
                      let uu____24671 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24671 = FStar_Syntax_Util.Equal  in
                    let uu____24672 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24672
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24676 = equal t1 t2  in
                         (if uu____24676
                          then
                            let uu____24679 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24679
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24684 =
                            let uu____24691 = equal t1 t2  in
                            if uu____24691
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24704 = mk_eq2 wl env orig t1 t2  in
                               match uu____24704 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24684 with
                          | (guard,wl1) ->
                              let uu____24725 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24725))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24728,uu____24729) ->
                  let head1 =
                    let uu____24737 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24737
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24783 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24783
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24829 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24829
                    then
                      let uu____24833 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24835 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24837 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24833 uu____24835 uu____24837
                    else ());
                   (let no_free_uvars t =
                      (let uu____24851 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24851) &&
                        (let uu____24855 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24855)
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
                      let uu____24874 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24874 = FStar_Syntax_Util.Equal  in
                    let uu____24875 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24875
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24879 = equal t1 t2  in
                         (if uu____24879
                          then
                            let uu____24882 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24882
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24887 =
                            let uu____24894 = equal t1 t2  in
                            if uu____24894
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24907 = mk_eq2 wl env orig t1 t2  in
                               match uu____24907 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24887 with
                          | (guard,wl1) ->
                              let uu____24928 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24928))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24931,uu____24932) ->
                  let head1 =
                    let uu____24934 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24934
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24980 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24980
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25026 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25026
                    then
                      let uu____25030 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25032 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25034 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25030 uu____25032 uu____25034
                    else ());
                   (let no_free_uvars t =
                      (let uu____25048 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25048) &&
                        (let uu____25052 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25052)
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
                      let uu____25071 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25071 = FStar_Syntax_Util.Equal  in
                    let uu____25072 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25072
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25076 = equal t1 t2  in
                         (if uu____25076
                          then
                            let uu____25079 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25079
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25084 =
                            let uu____25091 = equal t1 t2  in
                            if uu____25091
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25104 = mk_eq2 wl env orig t1 t2  in
                               match uu____25104 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25084 with
                          | (guard,wl1) ->
                              let uu____25125 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25125))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25128,uu____25129) ->
                  let head1 =
                    let uu____25131 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25131
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25177 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25177
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25223 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25223
                    then
                      let uu____25227 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25229 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25231 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25227 uu____25229 uu____25231
                    else ());
                   (let no_free_uvars t =
                      (let uu____25245 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25245) &&
                        (let uu____25249 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25249)
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
                      let uu____25268 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25268 = FStar_Syntax_Util.Equal  in
                    let uu____25269 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25269
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25273 = equal t1 t2  in
                         (if uu____25273
                          then
                            let uu____25276 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25276
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25281 =
                            let uu____25288 = equal t1 t2  in
                            if uu____25288
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25301 = mk_eq2 wl env orig t1 t2  in
                               match uu____25301 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25281 with
                          | (guard,wl1) ->
                              let uu____25322 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25322))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25325,uu____25326) ->
                  let head1 =
                    let uu____25328 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25328
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25368 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25368
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25408 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25408
                    then
                      let uu____25412 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25414 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25416 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25412 uu____25414 uu____25416
                    else ());
                   (let no_free_uvars t =
                      (let uu____25430 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25430) &&
                        (let uu____25434 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25434)
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
                      let uu____25453 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25453 = FStar_Syntax_Util.Equal  in
                    let uu____25454 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25454
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25458 = equal t1 t2  in
                         (if uu____25458
                          then
                            let uu____25461 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25461
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25466 =
                            let uu____25473 = equal t1 t2  in
                            if uu____25473
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25486 = mk_eq2 wl env orig t1 t2  in
                               match uu____25486 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25466 with
                          | (guard,wl1) ->
                              let uu____25507 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25507))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25510,uu____25511) ->
                  let head1 =
                    let uu____25529 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25529
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25569 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25569
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25609 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25609
                    then
                      let uu____25613 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25615 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25617 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25613 uu____25615 uu____25617
                    else ());
                   (let no_free_uvars t =
                      (let uu____25631 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25631) &&
                        (let uu____25635 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25635)
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
                      let uu____25654 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25654 = FStar_Syntax_Util.Equal  in
                    let uu____25655 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25655
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25659 = equal t1 t2  in
                         (if uu____25659
                          then
                            let uu____25662 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25662
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25667 =
                            let uu____25674 = equal t1 t2  in
                            if uu____25674
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25687 = mk_eq2 wl env orig t1 t2  in
                               match uu____25687 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25667 with
                          | (guard,wl1) ->
                              let uu____25708 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25708))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25711,FStar_Syntax_Syntax.Tm_match uu____25712) ->
                  let head1 =
                    let uu____25736 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25736
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25776 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25776
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25816 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25816
                    then
                      let uu____25820 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25822 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25824 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25820 uu____25822 uu____25824
                    else ());
                   (let no_free_uvars t =
                      (let uu____25838 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25838) &&
                        (let uu____25842 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25842)
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
                      let uu____25861 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25861 = FStar_Syntax_Util.Equal  in
                    let uu____25862 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25862
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25866 = equal t1 t2  in
                         (if uu____25866
                          then
                            let uu____25869 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25869
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25874 =
                            let uu____25881 = equal t1 t2  in
                            if uu____25881
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25894 = mk_eq2 wl env orig t1 t2  in
                               match uu____25894 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25874 with
                          | (guard,wl1) ->
                              let uu____25915 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25915))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25918,FStar_Syntax_Syntax.Tm_uinst uu____25919) ->
                  let head1 =
                    let uu____25927 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25927
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25967 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25967
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26007 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26007
                    then
                      let uu____26011 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26013 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26015 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26011 uu____26013 uu____26015
                    else ());
                   (let no_free_uvars t =
                      (let uu____26029 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26029) &&
                        (let uu____26033 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26033)
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
                      let uu____26052 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26052 = FStar_Syntax_Util.Equal  in
                    let uu____26053 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26053
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26057 = equal t1 t2  in
                         (if uu____26057
                          then
                            let uu____26060 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26060
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26065 =
                            let uu____26072 = equal t1 t2  in
                            if uu____26072
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26085 = mk_eq2 wl env orig t1 t2  in
                               match uu____26085 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26065 with
                          | (guard,wl1) ->
                              let uu____26106 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26106))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26109,FStar_Syntax_Syntax.Tm_name uu____26110) ->
                  let head1 =
                    let uu____26112 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26112
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26152 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26152
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26192 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26192
                    then
                      let uu____26196 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26198 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26200 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26196 uu____26198 uu____26200
                    else ());
                   (let no_free_uvars t =
                      (let uu____26214 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26214) &&
                        (let uu____26218 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26218)
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
                      let uu____26237 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26237 = FStar_Syntax_Util.Equal  in
                    let uu____26238 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26238
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26242 = equal t1 t2  in
                         (if uu____26242
                          then
                            let uu____26245 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26245
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26250 =
                            let uu____26257 = equal t1 t2  in
                            if uu____26257
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26270 = mk_eq2 wl env orig t1 t2  in
                               match uu____26270 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26250 with
                          | (guard,wl1) ->
                              let uu____26291 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26291))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26294,FStar_Syntax_Syntax.Tm_constant uu____26295) ->
                  let head1 =
                    let uu____26297 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26297
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26337 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26337
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26377 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26377
                    then
                      let uu____26381 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26383 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26385 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26381 uu____26383 uu____26385
                    else ());
                   (let no_free_uvars t =
                      (let uu____26399 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26399) &&
                        (let uu____26403 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26403)
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
                      let uu____26422 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26422 = FStar_Syntax_Util.Equal  in
                    let uu____26423 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26423
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26427 = equal t1 t2  in
                         (if uu____26427
                          then
                            let uu____26430 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26430
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26435 =
                            let uu____26442 = equal t1 t2  in
                            if uu____26442
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26455 = mk_eq2 wl env orig t1 t2  in
                               match uu____26455 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26435 with
                          | (guard,wl1) ->
                              let uu____26476 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26476))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26479,FStar_Syntax_Syntax.Tm_fvar uu____26480) ->
                  let head1 =
                    let uu____26482 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26482
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26528 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26528
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26574 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26574
                    then
                      let uu____26578 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26580 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26582 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26578 uu____26580 uu____26582
                    else ());
                   (let no_free_uvars t =
                      (let uu____26596 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26596) &&
                        (let uu____26600 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26600)
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
                      let uu____26619 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26619 = FStar_Syntax_Util.Equal  in
                    let uu____26620 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26620
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26624 = equal t1 t2  in
                         (if uu____26624
                          then
                            let uu____26627 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26627
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26632 =
                            let uu____26639 = equal t1 t2  in
                            if uu____26639
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26652 = mk_eq2 wl env orig t1 t2  in
                               match uu____26652 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26632 with
                          | (guard,wl1) ->
                              let uu____26673 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26673))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26676,FStar_Syntax_Syntax.Tm_app uu____26677) ->
                  let head1 =
                    let uu____26695 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26695
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26735 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26735
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26775 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26775
                    then
                      let uu____26779 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26781 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26783 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26779 uu____26781 uu____26783
                    else ());
                   (let no_free_uvars t =
                      (let uu____26797 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26797) &&
                        (let uu____26801 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26801)
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
                      let uu____26820 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26820 = FStar_Syntax_Util.Equal  in
                    let uu____26821 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26821
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26825 = equal t1 t2  in
                         (if uu____26825
                          then
                            let uu____26828 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26828
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26833 =
                            let uu____26840 = equal t1 t2  in
                            if uu____26840
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26853 = mk_eq2 wl env orig t1 t2  in
                               match uu____26853 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26833 with
                          | (guard,wl1) ->
                              let uu____26874 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26874))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26877,FStar_Syntax_Syntax.Tm_let uu____26878) ->
                  let uu____26905 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26905
                  then
                    let uu____26908 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26908
                  else
                    (let uu____26911 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26911 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26914,uu____26915) ->
                  let uu____26929 =
                    let uu____26935 =
                      let uu____26937 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26939 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26941 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26943 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26937 uu____26939 uu____26941 uu____26943
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26935)
                     in
                  FStar_Errors.raise_error uu____26929
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26947,FStar_Syntax_Syntax.Tm_let uu____26948) ->
                  let uu____26962 =
                    let uu____26968 =
                      let uu____26970 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26972 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26974 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26976 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26970 uu____26972 uu____26974 uu____26976
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26968)
                     in
                  FStar_Errors.raise_error uu____26962
                    t1.FStar_Syntax_Syntax.pos
              | uu____26980 ->
                  let uu____26985 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26985 orig))))

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
          (let uu____27051 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____27051
           then
             let uu____27056 =
               let uu____27058 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____27058  in
             let uu____27059 =
               let uu____27061 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____27061  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27056 uu____27059
           else ());
          (let uu____27065 =
             let uu____27067 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____27067  in
           if uu____27065
           then
             let uu____27070 =
               FStar_Thunk.mk
                 (fun uu____27075  ->
                    let uu____27076 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____27078 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27076 uu____27078)
                in
             giveup env uu____27070 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27100 =
                  FStar_Thunk.mk
                    (fun uu____27105  ->
                       let uu____27106 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27108 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27106 uu____27108)
                   in
                giveup env uu____27100 orig)
             else
               (let uu____27113 =
                  FStar_List.fold_left2
                    (fun uu____27134  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27134 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27155 =
                                 let uu____27160 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27161 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27160
                                   FStar_TypeChecker_Common.EQ uu____27161
                                   "effect universes"
                                  in
                               (match uu____27155 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27113 with
                | (univ_sub_probs,wl1) ->
                    let uu____27181 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27181 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27189 =
                           FStar_List.fold_right2
                             (fun uu____27226  ->
                                fun uu____27227  ->
                                  fun uu____27228  ->
                                    match (uu____27226, uu____27227,
                                            uu____27228)
                                    with
                                    | ((a1,uu____27272),(a2,uu____27274),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27307 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27307 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27189 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27334 =
                                  let uu____27337 =
                                    let uu____27340 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27340
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27337
                                   in
                                FStar_List.append univ_sub_probs uu____27334
                                 in
                              let guard =
                                let guard =
                                  let uu____27362 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27362  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3591_27371 = wl3  in
                                {
                                  attempting = (uu___3591_27371.attempting);
                                  wl_deferred = (uu___3591_27371.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3591_27371.wl_deferred_to_tac);
                                  ctr = (uu___3591_27371.ctr);
                                  defer_ok = (uu___3591_27371.defer_ok);
                                  smt_ok = (uu___3591_27371.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3591_27371.umax_heuristic_ok);
                                  tcenv = (uu___3591_27371.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27373 = attempt sub_probs wl5  in
                              solve env uu____27373))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____27391 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____27391
           then
             let uu____27396 =
               let uu____27398 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27398
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27400 =
               let uu____27402 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27402
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27396 uu____27400
           else ());
          (let uu____27407 =
             let uu____27412 =
               let uu____27417 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27417
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27412
               (fun uu____27434  ->
                  match uu____27434 with
                  | (c,g) ->
                      let uu____27445 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27445, g))
              in
           match uu____27407 with
           | (c12,g_lift) ->
               ((let uu____27449 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27449
                 then
                   let uu____27454 =
                     let uu____27456 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27456
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27458 =
                     let uu____27460 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27460
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27454 uu____27458
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3611_27470 = wl  in
                     {
                       attempting = (uu___3611_27470.attempting);
                       wl_deferred = (uu___3611_27470.wl_deferred);
                       wl_deferred_to_tac =
                         (uu___3611_27470.wl_deferred_to_tac);
                       ctr = (uu___3611_27470.ctr);
                       defer_ok = (uu___3611_27470.defer_ok);
                       smt_ok = (uu___3611_27470.smt_ok);
                       umax_heuristic_ok =
                         (uu___3611_27470.umax_heuristic_ok);
                       tcenv = (uu___3611_27470.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____27471 =
                     let rec is_uvar1 t =
                       let uu____27485 =
                         let uu____27486 = FStar_Syntax_Subst.compress t  in
                         uu____27486.FStar_Syntax_Syntax.n  in
                       match uu____27485 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27490 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27505) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27511) ->
                           is_uvar1 t1
                       | uu____27536 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27570  ->
                          fun uu____27571  ->
                            fun uu____27572  ->
                              match (uu____27570, uu____27571, uu____27572)
                              with
                              | ((a1,uu____27616),(a2,uu____27618),(is_sub_probs,wl2))
                                  ->
                                  let uu____27651 = is_uvar1 a1  in
                                  if uu____27651
                                  then
                                    ((let uu____27661 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27661
                                      then
                                        let uu____27666 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27668 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27666 uu____27668
                                      else ());
                                     (let uu____27673 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27673 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27471 with
                   | (is_sub_probs,wl2) ->
                       let uu____27701 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27701 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27709 =
                              let uu____27714 =
                                let uu____27715 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27715
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27714
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27709 with
                             | (uu____27722,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27733 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27735 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27733 s uu____27735
                                    in
                                 let uu____27738 =
                                   let uu____27767 =
                                     let uu____27768 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27768.FStar_Syntax_Syntax.n  in
                                   match uu____27767 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27828 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27828 with
                                        | (a::bs1,c3) ->
                                            let uu____27884 =
                                              let uu____27903 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27903
                                                (fun uu____28007  ->
                                                   match uu____28007 with
                                                   | (l1,l2) ->
                                                       let uu____28080 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____28080))
                                               in
                                            (match uu____27884 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____28185 ->
                                       let uu____28186 =
                                         let uu____28192 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____28192)
                                          in
                                       FStar_Errors.raise_error uu____28186 r
                                    in
                                 (match uu____27738 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____28268 =
                                        let uu____28275 =
                                          let uu____28276 =
                                            let uu____28277 =
                                              let uu____28284 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____28284,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____28277
                                             in
                                          [uu____28276]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____28275
                                          (fun b  ->
                                             let uu____28300 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____28302 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28304 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____28300 uu____28302
                                               uu____28304) r
                                         in
                                      (match uu____28268 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____28314 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____28314
                                             then
                                               let uu____28319 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____28328 =
                                                          let uu____28330 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____28330
                                                           in
                                                        Prims.op_Hat s
                                                          uu____28328) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____28319
                                             else ());
                                            (let wl4 =
                                               let uu___3683_28338 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3683_28338.attempting);
                                                 wl_deferred =
                                                   (uu___3683_28338.wl_deferred);
                                                 wl_deferred_to_tac =
                                                   (uu___3683_28338.wl_deferred_to_tac);
                                                 ctr = (uu___3683_28338.ctr);
                                                 defer_ok =
                                                   (uu___3683_28338.defer_ok);
                                                 smt_ok =
                                                   (uu___3683_28338.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3683_28338.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3683_28338.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____28363 =
                                                        let uu____28370 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____28370, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____28363) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____28387 =
                                               let f_sort_is =
                                                 let uu____28397 =
                                                   let uu____28398 =
                                                     let uu____28401 =
                                                       let uu____28402 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28402.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28401
                                                      in
                                                   uu____28398.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28397 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28413,uu____28414::is)
                                                     ->
                                                     let uu____28456 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28456
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28489 ->
                                                     let uu____28490 =
                                                       let uu____28496 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28496)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28490 r
                                                  in
                                               let uu____28502 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28537  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28537
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28558 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28558
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28502
                                                in
                                             match uu____28387 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28583 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28583
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28584 =
                                                   let g_sort_is =
                                                     let uu____28594 =
                                                       let uu____28595 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28595.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28594 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28600,uu____28601::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28661 ->
                                                         let uu____28662 =
                                                           let uu____28668 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28668)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28662 r
                                                      in
                                                   let uu____28674 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28709  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28709
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28730
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28730
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28674
                                                    in
                                                 (match uu____28584 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28757 =
                                                          let uu____28762 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28763 =
                                                            let uu____28764 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28764
                                                             in
                                                          (uu____28762,
                                                            uu____28763)
                                                           in
                                                        match uu____28757
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28792 =
                                                          let uu____28795 =
                                                            let uu____28798 =
                                                              let uu____28801
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28801
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28798
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28795
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28792
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28825 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28825
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
                                                        let uu____28836 =
                                                          let uu____28839 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28842  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28842)
                                                            uu____28839
                                                           in
                                                        solve_prob orig
                                                          uu____28836 [] wl6
                                                         in
                                                      let uu____28843 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28843))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28866 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28868 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28868]
              | x -> x  in
            let c12 =
              let uu___3749_28871 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3749_28871.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3749_28871.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3749_28871.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3749_28871.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28872 =
              let uu____28877 =
                FStar_All.pipe_right
                  (let uu___3752_28879 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3752_28879.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3752_28879.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3752_28879.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3752_28879.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28877
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28872
              (fun uu____28893  ->
                 match uu____28893 with
                 | (c,g) ->
                     let uu____28900 =
                       let uu____28902 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28902  in
                     if uu____28900
                     then
                       let uu____28905 =
                         let uu____28911 =
                           let uu____28913 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28915 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28913 uu____28915
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28911)
                          in
                       FStar_Errors.raise_error uu____28905 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28921 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28921
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28927 = lift_c1 ()  in
               solve_eq uu____28927 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28936  ->
                         match uu___31_28936 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28941 -> false))
                  in
               let uu____28943 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28973)::uu____28974,(wp2,uu____28976)::uu____28977)
                     -> (wp1, wp2)
                 | uu____29050 ->
                     let uu____29075 =
                       let uu____29081 =
                         let uu____29083 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____29085 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____29083 uu____29085
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____29081)
                        in
                     FStar_Errors.raise_error uu____29075
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28943 with
               | (wpc1,wpc2) ->
                   let uu____29095 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____29095
                   then
                     let uu____29098 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29098 wl
                   else
                     (let uu____29102 =
                        let uu____29109 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____29109  in
                      match uu____29102 with
                      | (c2_decl,qualifiers) ->
                          let uu____29130 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____29130
                          then
                            let c1_repr =
                              let uu____29137 =
                                let uu____29138 =
                                  let uu____29139 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____29139  in
                                let uu____29140 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29138 uu____29140
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29137
                               in
                            let c2_repr =
                              let uu____29143 =
                                let uu____29144 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____29145 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29144 uu____29145
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29143
                               in
                            let uu____29147 =
                              let uu____29152 =
                                let uu____29154 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____29156 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____29154
                                  uu____29156
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____29152
                               in
                            (match uu____29147 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____29162 = attempt [prob] wl2  in
                                 solve env uu____29162)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____29182 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____29182
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____29205 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____29205
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
                                        let uu____29215 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____29215 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____29222 =
                                        let uu____29229 =
                                          let uu____29230 =
                                            let uu____29247 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____29250 =
                                              let uu____29261 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____29261; wpc1_2]  in
                                            (uu____29247, uu____29250)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____29230
                                           in
                                        FStar_Syntax_Syntax.mk uu____29229
                                         in
                                      uu____29222
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
                                     let uu____29310 =
                                       let uu____29317 =
                                         let uu____29318 =
                                           let uu____29335 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____29338 =
                                             let uu____29349 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____29358 =
                                               let uu____29369 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____29369; wpc1_2]  in
                                             uu____29349 :: uu____29358  in
                                           (uu____29335, uu____29338)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____29318
                                          in
                                       FStar_Syntax_Syntax.mk uu____29317  in
                                     uu____29310 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____29423 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____29423
                              then
                                let uu____29428 =
                                  let uu____29430 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____29430
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____29428
                              else ());
                             (let uu____29434 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____29434 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____29443 =
                                      let uu____29446 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _29449  ->
                                           FStar_Pervasives_Native.Some
                                             _29449) uu____29446
                                       in
                                    solve_prob orig uu____29443 [] wl1  in
                                  let uu____29450 = attempt [base_prob] wl2
                                     in
                                  solve env uu____29450))))
           in
        let uu____29451 = FStar_Util.physical_equality c1 c2  in
        if uu____29451
        then
          let uu____29454 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29454
        else
          ((let uu____29458 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29458
            then
              let uu____29463 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29465 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29463
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29465
            else ());
           (let uu____29470 =
              let uu____29479 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29482 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29479, uu____29482)  in
            match uu____29470 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29500),FStar_Syntax_Syntax.Total
                    (t2,uu____29502)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29519 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29519 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29521,FStar_Syntax_Syntax.Total uu____29522) ->
                     let uu____29539 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29539 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29543),FStar_Syntax_Syntax.Total
                    (t2,uu____29545)) ->
                     let uu____29562 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29562 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29565),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29567)) ->
                     let uu____29584 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29584 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29587),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29589)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29606 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29606 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29609),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29611)) ->
                     let uu____29628 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29628 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29631,FStar_Syntax_Syntax.Comp uu____29632) ->
                     let uu____29641 =
                       let uu___3876_29644 = problem  in
                       let uu____29647 =
                         let uu____29648 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29648
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3876_29644.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29647;
                         FStar_TypeChecker_Common.relation =
                           (uu___3876_29644.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3876_29644.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3876_29644.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3876_29644.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3876_29644.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3876_29644.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3876_29644.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3876_29644.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29641 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29649,FStar_Syntax_Syntax.Comp uu____29650) ->
                     let uu____29659 =
                       let uu___3876_29662 = problem  in
                       let uu____29665 =
                         let uu____29666 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29666
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3876_29662.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29665;
                         FStar_TypeChecker_Common.relation =
                           (uu___3876_29662.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3876_29662.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3876_29662.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3876_29662.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3876_29662.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3876_29662.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3876_29662.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3876_29662.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29659 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29667,FStar_Syntax_Syntax.GTotal uu____29668) ->
                     let uu____29677 =
                       let uu___3888_29680 = problem  in
                       let uu____29683 =
                         let uu____29684 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29684
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3888_29680.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3888_29680.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3888_29680.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29683;
                         FStar_TypeChecker_Common.element =
                           (uu___3888_29680.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3888_29680.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3888_29680.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3888_29680.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3888_29680.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3888_29680.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29677 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29685,FStar_Syntax_Syntax.Total uu____29686) ->
                     let uu____29695 =
                       let uu___3888_29698 = problem  in
                       let uu____29701 =
                         let uu____29702 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29702
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3888_29698.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3888_29698.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3888_29698.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29701;
                         FStar_TypeChecker_Common.element =
                           (uu___3888_29698.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3888_29698.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3888_29698.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3888_29698.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3888_29698.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3888_29698.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29695 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29703,FStar_Syntax_Syntax.Comp uu____29704) ->
                     let uu____29705 =
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
                     if uu____29705
                     then
                       let uu____29708 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29708 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29715 =
                            let uu____29720 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29720
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29729 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29730 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29729, uu____29730))
                             in
                          match uu____29715 with
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
                           (let uu____29738 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29738
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29746 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29746 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29749 =
                                  FStar_Thunk.mk
                                    (fun uu____29754  ->
                                       let uu____29755 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29757 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29755 uu____29757)
                                   in
                                giveup env uu____29749 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29768 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29768 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29818 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29818 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29843 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29874  ->
                match uu____29874 with
                | (u1,u2) ->
                    let uu____29882 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29884 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29882 uu____29884))
         in
      FStar_All.pipe_right uu____29843 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29921,[])) when
          let uu____29948 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29948 -> "{}"
      | uu____29951 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29978 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29978
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry defs =
            let uu____30009 =
              FStar_List.map
                (fun uu____30023  ->
                   match uu____30023 with
                   | (msg,x) ->
                       let uu____30034 =
                         let uu____30036 = prob_to_string env x  in
                         Prims.op_Hat ": " uu____30036  in
                       Prims.op_Hat msg uu____30034) defs
               in
            FStar_All.pipe_right uu____30009 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30046 = carry g.FStar_TypeChecker_Common.deferred  in
          let uu____30048 = carry g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____30050 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30046 uu____30048 uu____30050 imps
  
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
                  let uu____30107 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30107
                  then
                    let uu____30115 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30117 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30115
                      (rel_to_string rel) uu____30117
                  else "TOP"  in
                let uu____30123 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30123 with
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
              let uu____30183 =
                let uu____30186 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _30189  -> FStar_Pervasives_Native.Some _30189)
                  uu____30186
                 in
              FStar_Syntax_Syntax.new_bv uu____30183 t1  in
            let uu____30190 =
              let uu____30195 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30195
               in
            match uu____30190 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____30267 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30267
         then
           let uu____30272 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30272
         else ());
        (let uu____30279 =
           FStar_Util.record_time (fun uu____30286  -> solve env probs)  in
         match uu____30279 with
         | (sol,ms) ->
             ((let uu____30300 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30300
               then
                 let uu____30305 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30305
               else ());
              (match sol with
               | Success (deferred,defer_to_tac,implicits) ->
                   let uu____30321 =
                     FStar_Util.record_time
                       (fun uu____30328  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30321 with
                    | ((),ms1) ->
                        ((let uu____30341 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30341
                          then
                            let uu____30346 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30346
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d,s) ->
                   ((let uu____30360 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30360
                     then
                       let uu____30367 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30367
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
          ((let uu____30395 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30395
            then
              let uu____30400 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30400
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30408 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30408
             then
               let uu____30413 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30413
             else ());
            (let f2 =
               let uu____30419 =
                 let uu____30420 = FStar_Syntax_Util.unmeta f1  in
                 uu____30420.FStar_Syntax_Syntax.n  in
               match uu____30419 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30424 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4007_30425 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4007_30425.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4007_30425.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4007_30425.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4007_30425.FStar_TypeChecker_Common.implicits)
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
            let uu____30477 =
              let uu____30478 =
                let uu____30479 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _30480  ->
                       FStar_TypeChecker_Common.NonTrivial _30480)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30479;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30478  in
            FStar_All.pipe_left
              (fun _30487  -> FStar_Pervasives_Native.Some _30487)
              uu____30477
  
let with_guard_no_simp :
  'Auu____30497 .
    'Auu____30497 ->
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
            let uu____30546 =
              let uu____30547 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _30548  -> FStar_TypeChecker_Common.NonTrivial _30548)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30547;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30546
  
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
          (let uu____30581 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30581
           then
             let uu____30586 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30588 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30586
               uu____30588
           else ());
          (let uu____30593 =
             let uu____30598 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30598
              in
           match uu____30593 with
           | (prob,wl) ->
               let g =
                 let uu____30606 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30616  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30606  in
               ((let uu____30638 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30638
                 then
                   let uu____30643 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30643
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
        let uu____30664 = try_teq true env t1 t2  in
        match uu____30664 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30669 = FStar_TypeChecker_Env.get_range env  in
              let uu____30670 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30669 uu____30670);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30678 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30678
              then
                let uu____30683 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30685 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30687 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30683
                  uu____30685 uu____30687
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
        (let uu____30711 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30711
         then
           let uu____30716 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30718 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30716
             uu____30718
         else ());
        (let uu____30723 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30723 with
         | (prob,x,wl) ->
             let g =
               let uu____30738 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30749  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30738  in
             ((let uu____30771 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30771
               then
                 let uu____30776 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30776
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30784 =
                     let uu____30785 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30785 g1  in
                   FStar_Pervasives_Native.Some uu____30784)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30807 = FStar_TypeChecker_Env.get_range env  in
          let uu____30808 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30807 uu____30808
  
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
        (let uu____30837 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30837
         then
           let uu____30842 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30844 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30842 uu____30844
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30855 =
           let uu____30862 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30862 "sub_comp"
            in
         match uu____30855 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30875 =
                 FStar_Util.record_time
                   (fun uu____30887  ->
                      let uu____30888 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30899  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30888)
                  in
               match uu____30875 with
               | (r,ms) ->
                   ((let uu____30931 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30931
                     then
                       let uu____30936 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30938 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30940 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30936 uu____30938
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30940
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
      fun uu____30978  ->
        match uu____30978 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31021 =
                 let uu____31027 =
                   let uu____31029 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31031 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31029 uu____31031
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31027)  in
               let uu____31035 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31021 uu____31035)
               in
            let equiv1 v1 v' =
              let uu____31048 =
                let uu____31053 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____31054 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31053, uu____31054)  in
              match uu____31048 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31074 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____31105 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____31105 with
                      | FStar_Syntax_Syntax.U_unif uu____31112 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31141  ->
                                    match uu____31141 with
                                    | (u,v') ->
                                        let uu____31150 = equiv1 v1 v'  in
                                        if uu____31150
                                        then
                                          let uu____31155 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____31155 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____31176 -> []))
               in
            let uu____31181 =
              let wl =
                let uu___4120_31185 = empty_worklist env  in
                {
                  attempting = (uu___4120_31185.attempting);
                  wl_deferred = (uu___4120_31185.wl_deferred);
                  wl_deferred_to_tac = (uu___4120_31185.wl_deferred_to_tac);
                  ctr = (uu___4120_31185.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4120_31185.smt_ok);
                  umax_heuristic_ok = (uu___4120_31185.umax_heuristic_ok);
                  tcenv = (uu___4120_31185.tcenv);
                  wl_implicits = (uu___4120_31185.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31204  ->
                      match uu____31204 with
                      | (lb,v1) ->
                          let uu____31211 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____31211 with
                           | USolved wl1 -> ()
                           | uu____31214 -> fail1 lb v1)))
               in
            let rec check_ineq uu____31225 =
              match uu____31225 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31237) -> true
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
                      uu____31261,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31263,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31274) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____31282,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____31291 -> false)
               in
            let uu____31297 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31314  ->
                      match uu____31314 with
                      | (u,v1) ->
                          let uu____31322 = check_ineq (u, v1)  in
                          if uu____31322
                          then true
                          else
                            ((let uu____31330 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31330
                              then
                                let uu____31335 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31337 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____31335
                                  uu____31337
                              else ());
                             false)))
               in
            if uu____31297
            then ()
            else
              ((let uu____31347 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31347
                then
                  ((let uu____31353 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31353);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31365 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31365))
                else ());
               (let uu____31378 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31378))
  
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
        let fail1 uu____31453 =
          match uu____31453 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4197_31480 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4197_31480.attempting);
            wl_deferred = (uu___4197_31480.wl_deferred);
            wl_deferred_to_tac = (uu___4197_31480.wl_deferred_to_tac);
            ctr = (uu___4197_31480.ctr);
            defer_ok;
            smt_ok = (uu___4197_31480.smt_ok);
            umax_heuristic_ok = (uu___4197_31480.umax_heuristic_ok);
            tcenv = (uu___4197_31480.tcenv);
            wl_implicits = (uu___4197_31480.wl_implicits)
          }  in
        (let uu____31483 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31483
         then
           let uu____31488 = FStar_Util.string_of_bool defer_ok  in
           let uu____31490 = wl_to_string wl  in
           let uu____31492 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____31488 uu____31490 uu____31492
         else ());
        (let g1 =
           let uu____31498 = solve_and_commit env wl fail1  in
           match uu____31498 with
           | FStar_Pervasives_Native.Some
               (uu____31507::uu____31508,uu____31509,uu____31510) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,defer_to_tac,imps) ->
               let uu___4214_31544 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4214_31544.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred_to_tac =
                   (FStar_List.append
                      g.FStar_TypeChecker_Common.deferred_to_tac defer_to_tac);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4214_31544.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____31550 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4219_31561 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4219_31561.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4219_31561.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4219_31561.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4219_31561.FStar_TypeChecker_Common.implicits)
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
          (let uu____31637 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____31637
           then
             let uu____31642 = guard_to_string env g  in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31642
           else ());
          (let g1 = solve_deferred_constraints env g  in
           let ret_g =
             let uu___4233_31649 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4233_31649.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4233_31649.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4233_31649.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4233_31649.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31650 =
             let uu____31652 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31652  in
           if uu____31650
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug1
                   then
                     (let uu____31664 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31665 =
                        let uu____31667 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31667
                         in
                      FStar_Errors.diag uu____31664 uu____31665)
                   else ();
                   (let vc1 =
                      let uu____31673 =
                        let uu____31677 =
                          let uu____31679 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31679  in
                        FStar_Pervasives_Native.Some uu____31677  in
                      FStar_Profiling.profile
                        (fun uu____31682  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31673 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug1
                    then
                      (let uu____31686 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31687 =
                         let uu____31689 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31689
                          in
                       FStar_Errors.diag uu____31686 uu____31687)
                    else ();
                    (let uu____31695 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31695 "discharge_guard'" env vc1);
                    (let uu____31697 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31697 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug1
                            then
                              (let uu____31706 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31707 =
                                 let uu____31709 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31709
                                  in
                               FStar_Errors.diag uu____31706 uu____31707)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug1
                            then
                              (let uu____31719 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31720 =
                                 let uu____31722 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31722
                                  in
                               FStar_Errors.diag uu____31719 uu____31720)
                            else ();
                            (let vcs =
                               let uu____31736 = FStar_Options.use_tactics ()
                                  in
                               if uu____31736
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31758  ->
                                      (let uu____31760 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left (fun a1  -> ())
                                         uu____31760);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31804  ->
                                               match uu____31804 with
                                               | (env1,goal,opts) ->
                                                   let uu____31820 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____31820, opts)))))
                               else
                                 (let uu____31824 =
                                    let uu____31831 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____31831)  in
                                  [uu____31824])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____31864  ->
                                     match uu____31864 with
                                     | (env1,goal,opts) ->
                                         let uu____31874 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____31874 with
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
                                                 (let uu____31885 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31886 =
                                                    let uu____31888 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____31890 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____31888 uu____31890
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31885 uu____31886)
                                               else ();
                                               if debug1
                                               then
                                                 (let uu____31897 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31898 =
                                                    let uu____31900 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____31900
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31897 uu____31898)
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
      let uu____31918 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31918 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31927 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31927
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31941 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31941 with
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
        let uu____31971 = try_teq false env t1 t2  in
        match uu____31971 with
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
            let uu____32015 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32015 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32022 ->
                     let uu____32023 =
                       let uu____32024 = FStar_Syntax_Subst.compress r  in
                       uu____32024.FStar_Syntax_Syntax.n  in
                     (match uu____32023 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32029) ->
                          unresolved ctx_u'
                      | uu____32046 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32070 = acc  in
            match uu____32070 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____32089 = hd1  in
                     (match uu____32089 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____32100 = unresolved ctx_u  in
                             if uu____32100
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32111 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32111
                                     then
                                       let uu____32115 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32115
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32124 = teq_nosmt env1 t tm
                                          in
                                       match uu____32124 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4346_32134 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4346_32134.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4346_32134.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4346_32134.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4346_32134.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4346_32134.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4346_32134.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4346_32134.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4349_32136 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4349_32136.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4349_32136.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4349_32136.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                               | uu____32139 ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4354_32151 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4354_32151.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4354_32151.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4354_32151.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4354_32151.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4354_32151.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4354_32151.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4354_32151.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4354_32151.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4354_32151.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4354_32151.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4354_32151.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4354_32151.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4354_32151.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4354_32151.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4354_32151.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4354_32151.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4354_32151.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4354_32151.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4354_32151.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4354_32151.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4354_32151.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4354_32151.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4354_32151.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4354_32151.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4354_32151.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4354_32151.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4354_32151.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4354_32151.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4354_32151.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4354_32151.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4354_32151.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4354_32151.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4354_32151.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4354_32151.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4354_32151.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4354_32151.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4354_32151.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4354_32151.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4354_32151.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4354_32151.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4354_32151.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4354_32151.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4354_32151.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4354_32151.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4354_32151.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4354_32151.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___4354_32151.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4359_32156 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4359_32156.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4359_32156.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4359_32156.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4359_32156.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4359_32156.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4359_32156.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4359_32156.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4359_32156.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4359_32156.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4359_32156.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4359_32156.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4359_32156.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4359_32156.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4359_32156.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4359_32156.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4359_32156.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4359_32156.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4359_32156.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4359_32156.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4359_32156.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4359_32156.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4359_32156.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4359_32156.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4359_32156.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4359_32156.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4359_32156.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4359_32156.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4359_32156.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4359_32156.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4359_32156.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4359_32156.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4359_32156.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4359_32156.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4359_32156.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4359_32156.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4359_32156.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4359_32156.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      }
                                    else env1  in
                                  (let uu____32161 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32161
                                   then
                                     let uu____32166 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32168 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32170 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32172 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32166 uu____32168 uu____32170
                                       reason uu____32172
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4365_32179  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32186 =
                                             let uu____32196 =
                                               let uu____32204 =
                                                 let uu____32206 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32208 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32210 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32206 uu____32208
                                                   uu____32210
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32204, r)
                                                in
                                             [uu____32196]  in
                                           FStar_Errors.add_errors
                                             uu____32186);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32229 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32240  ->
                                               let uu____32241 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32243 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32245 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32241 uu____32243
                                                 reason uu____32245)) env2 g1
                                         true
                                        in
                                     match uu____32229 with
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
          let uu___4377_32253 = g  in
          let uu____32254 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4377_32253.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4377_32253.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4377_32253.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4377_32253.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32254
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____32269 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32269
       then
         let uu____32274 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32274
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
      (let uu____32305 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32305
       then
         let uu____32310 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32310
       else ());
      (let solve_goals_with_tac imps tac =
         let deferred_goals =
           FStar_TypeChecker_DeferredImplicits.sort_goals env imps  in
         let guard =
           let uu___4393_32328 = g  in
           {
             FStar_TypeChecker_Common.guard_f =
               (uu___4393_32328.FStar_TypeChecker_Common.guard_f);
             FStar_TypeChecker_Common.deferred_to_tac = [];
             FStar_TypeChecker_Common.deferred =
               (uu___4393_32328.FStar_TypeChecker_Common.deferred);
             FStar_TypeChecker_Common.univ_ineqs =
               (uu___4393_32328.FStar_TypeChecker_Common.univ_ineqs);
             FStar_TypeChecker_Common.implicits = imps
           }  in
         let resolve_tac =
           match tac.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_let (uu____32335,lid::[]) ->
               let qn = FStar_TypeChecker_Env.lookup_qname env lid  in
               let fv =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   (FStar_Syntax_Syntax.Delta_constant_at_level
                      Prims.int_zero) FStar_Pervasives_Native.None
                  in
               let dd =
                 let uu____32343 =
                   FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn  in
                 match uu____32343 with
                 | FStar_Pervasives_Native.Some dd -> dd
                 | FStar_Pervasives_Native.None  -> failwith "Expected a dd"
                  in
               let term =
                 let uu____32349 =
                   FStar_Syntax_Syntax.lid_as_fv lid dd
                     FStar_Pervasives_Native.None
                    in
                 FStar_Syntax_Syntax.fv_to_tm uu____32349  in
               term
           | uu____32350 -> failwith "Resolve_tac not found"  in
         let env1 =
           let uu___4410_32353 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___4410_32353.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___4410_32353.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___4410_32353.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___4410_32353.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___4410_32353.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___4410_32353.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___4410_32353.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___4410_32353.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___4410_32353.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___4410_32353.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___4410_32353.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___4410_32353.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___4410_32353.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___4410_32353.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___4410_32353.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___4410_32353.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___4410_32353.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict =
               (uu___4410_32353.FStar_TypeChecker_Env.use_eq_strict);
             FStar_TypeChecker_Env.is_iface =
               (uu___4410_32353.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___4410_32353.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___4410_32353.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___4410_32353.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___4410_32353.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___4410_32353.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___4410_32353.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___4410_32353.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___4410_32353.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___4410_32353.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___4410_32353.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___4410_32353.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___4410_32353.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___4410_32353.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___4410_32353.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___4410_32353.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___4410_32353.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___4410_32353.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___4410_32353.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___4410_32353.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___4410_32353.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___4410_32353.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___4410_32353.FStar_TypeChecker_Env.is_native_tactic);
             FStar_TypeChecker_Env.identifier_info =
               (uu___4410_32353.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___4410_32353.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___4410_32353.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___4410_32353.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___4410_32353.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___4410_32353.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac = false
           }  in
         env1.FStar_TypeChecker_Env.try_solve_implicits_hook env1 resolve_tac
           deferred_goals
          in
       let solve_deferred_to_tactic g1 =
         let deferred = g1.FStar_TypeChecker_Common.deferred_to_tac  in
         match deferred with
         | [] -> g1
         | uu____32367 ->
             let prob_as_implicit uu____32382 =
               match uu____32382 with
               | (reason,prob) ->
                   (match prob with
                    | FStar_TypeChecker_Common.TProb tp when
                        tp.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ
                        ->
                        let env1 =
                          let uu___4424_32404 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4424_32404.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4424_32404.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4424_32404.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              ((tp.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4424_32404.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4424_32404.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4424_32404.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4424_32404.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4424_32404.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4424_32404.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4424_32404.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4424_32404.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4424_32404.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4424_32404.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4424_32404.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4424_32404.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4424_32404.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4424_32404.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4424_32404.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4424_32404.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___4424_32404.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4424_32404.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4424_32404.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4424_32404.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4424_32404.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4424_32404.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4424_32404.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4424_32404.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4424_32404.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4424_32404.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___4424_32404.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4424_32404.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4424_32404.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4424_32404.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4424_32404.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4424_32404.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4424_32404.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4424_32404.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4424_32404.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4424_32404.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___4424_32404.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4424_32404.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4424_32404.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4424_32404.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4424_32404.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4424_32404.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4424_32404.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4424_32404.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let env_lax =
                          let uu___4427_32406 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4427_32406.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4427_32406.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4427_32406.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___4427_32406.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4427_32406.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4427_32406.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4427_32406.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4427_32406.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4427_32406.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4427_32406.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4427_32406.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4427_32406.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4427_32406.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4427_32406.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4427_32406.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4427_32406.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4427_32406.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4427_32406.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4427_32406.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4427_32406.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4427_32406.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4427_32406.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4427_32406.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4427_32406.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4427_32406.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4427_32406.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4427_32406.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4427_32406.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4427_32406.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts = true;
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4427_32406.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4427_32406.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4427_32406.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4427_32406.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4427_32406.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4427_32406.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4427_32406.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4427_32406.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4427_32406.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___4427_32406.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4427_32406.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4427_32406.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4427_32406.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4427_32406.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4427_32406.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4427_32406.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4427_32406.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let uu____32409 =
                          env1.FStar_TypeChecker_Env.type_of env_lax
                            tp.FStar_TypeChecker_Common.lhs
                           in
                        (match uu____32409 with
                         | (uu____32420,tlhs,uu____32422) ->
                             let goal_ty =
                               let uu____32424 =
                                 env1.FStar_TypeChecker_Env.universe_of
                                   env_lax tlhs
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____32424 tlhs
                                 tp.FStar_TypeChecker_Common.lhs
                                 tp.FStar_TypeChecker_Common.rhs
                                in
                             let uu____32425 =
                               FStar_TypeChecker_Env.new_implicit_var_aux
                                 reason
                                 (tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos
                                 env1 goal_ty
                                 FStar_Syntax_Syntax.Allow_untyped
                                 FStar_Pervasives_Native.None
                                in
                             (match uu____32425 with
                              | (goal,ctx_uvar,uu____32444) ->
                                  let imp =
                                    let uu____32458 =
                                      let uu____32459 =
                                        FStar_List.hd ctx_uvar  in
                                      FStar_Pervasives_Native.fst uu____32459
                                       in
                                    {
                                      FStar_TypeChecker_Common.imp_reason =
                                        "";
                                      FStar_TypeChecker_Common.imp_uvar =
                                        uu____32458;
                                      FStar_TypeChecker_Common.imp_tm = goal;
                                      FStar_TypeChecker_Common.imp_range =
                                        ((tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos)
                                    }  in
                                  let sigelt =
                                    let uu____32472 =
                                      is_flex tp.FStar_TypeChecker_Common.lhs
                                       in
                                    if uu____32472
                                    then
                                      let uu____32477 =
                                        flex_uvar_head
                                          tp.FStar_TypeChecker_Common.lhs
                                         in
                                      find_user_tac_for_uvar env1 uu____32477
                                    else
                                      (let uu____32480 =
                                         is_flex
                                           tp.FStar_TypeChecker_Common.rhs
                                          in
                                       if uu____32480
                                       then
                                         let uu____32485 =
                                           flex_uvar_head
                                             tp.FStar_TypeChecker_Common.rhs
                                            in
                                         find_user_tac_for_uvar env1
                                           uu____32485
                                       else FStar_Pervasives_Native.None)
                                     in
                                  (match sigelt with
                                   | FStar_Pervasives_Native.None  ->
                                       failwith
                                         "Impossible: No tactic associated with deferred problem"
                                   | FStar_Pervasives_Native.Some se ->
                                       (imp, se))))
                    | uu____32498 ->
                        failwith "Unexpected problem deferred to tactic")
                in
             let eqs =
               FStar_List.map prob_as_implicit
                 g1.FStar_TypeChecker_Common.deferred_to_tac
                in
             let uu____32520 =
               FStar_List.fold_right
                 (fun imp  ->
                    fun uu____32552  ->
                      match uu____32552 with
                      | (more,imps) ->
                          let uu____32595 =
                            FStar_Syntax_Unionfind.find
                              (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                             in
                          (match uu____32595 with
                           | FStar_Pervasives_Native.Some uu____32610 ->
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
                                            let uu____32649 =
                                              FStar_Syntax_Print.term_to_string
                                                a
                                               in
                                            FStar_Util.format2 "%s::%s"
                                              uu____32649
                                              imp.FStar_TypeChecker_Common.imp_reason
                                             in
                                          let uu___4463_32652 = imp  in
                                          {
                                            FStar_TypeChecker_Common.imp_reason
                                              = reason;
                                            FStar_TypeChecker_Common.imp_uvar
                                              =
                                              (uu___4463_32652.FStar_TypeChecker_Common.imp_uvar);
                                            FStar_TypeChecker_Common.imp_tm =
                                              (uu___4463_32652.FStar_TypeChecker_Common.imp_tm);
                                            FStar_TypeChecker_Common.imp_range
                                              =
                                              (uu___4463_32652.FStar_TypeChecker_Common.imp_range)
                                          }
                                      | uu____32653 -> imp  in
                                    (((imp1, se1) :: more), imps))))
                 g1.FStar_TypeChecker_Common.implicits ([], [])
                in
             (match uu____32520 with
              | (more,imps) ->
                  let bucketize is =
                    let map1 = FStar_Util.smap_create (Prims.of_int (17))  in
                    FStar_List.iter
                      (fun uu____32749  ->
                         match uu____32749 with
                         | (i,s) ->
                             let uu____32756 =
                               FStar_Syntax_Util.lid_of_sigelt s  in
                             (match uu____32756 with
                              | FStar_Pervasives_Native.None  ->
                                  failwith
                                    "Unexpected: tactic without a name"
                              | FStar_Pervasives_Native.Some l ->
                                  let uu____32761 =
                                    FStar_Util.smap_try_find map1
                                      l.FStar_Ident.nsstr
                                     in
                                  (match uu____32761 with
                                   | FStar_Pervasives_Native.None  ->
                                       FStar_Util.smap_add map1
                                         l.FStar_Ident.nsstr ([i], s)
                                   | FStar_Pervasives_Native.Some (is1,s1) ->
                                       (FStar_Util.smap_remove map1
                                          l.FStar_Ident.nsstr;
                                        FStar_Util.smap_add map1
                                          l.FStar_Ident.nsstr
                                          ((i :: is1), s1))))) is;
                    FStar_Util.smap_fold map1
                      (fun uu____32808  -> fun is1  -> fun out  -> is1 :: out)
                      []
                     in
                  let buckets = bucketize (FStar_List.append eqs more)  in
                  (FStar_List.iter
                     (fun uu____32849  ->
                        match uu____32849 with
                        | (imps1,sigel) -> solve_goals_with_tac imps1 sigel)
                     buckets;
                   (let uu___4494_32856 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___4494_32856.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac = [];
                      FStar_TypeChecker_Common.deferred =
                        (uu___4494_32856.FStar_TypeChecker_Common.deferred);
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___4494_32856.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits = imps
                    })))
          in
       let g1 = solve_deferred_constraints env g  in
       let g2 = solve_deferred_to_tactic g1  in
       (let uu____32865 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ResolveImplicitsHook")
           in
        if uu____32865
        then
          let uu____32870 = guard_to_string env g2  in
          FStar_Util.print1
            "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
            uu____32870
        else ());
       (let g3 = resolve_implicits env g2  in
        match g3.FStar_TypeChecker_Common.implicits with
        | [] ->
            let uu____32876 = discharge_guard env g3  in
            FStar_All.pipe_left (fun a2  -> ()) uu____32876
        | imp::uu____32878 ->
            let uu____32881 =
              let uu____32887 =
                let uu____32889 =
                  FStar_Syntax_Print.uvar_to_string
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                   in
                let uu____32891 =
                  FStar_TypeChecker_Normalize.term_to_string env
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                   in
                FStar_Util.format3
                  "Failed to resolve implicit argument %s of type %s introduced for %s"
                  uu____32889 uu____32891
                  imp.FStar_TypeChecker_Common.imp_reason
                 in
              (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32887)
               in
            FStar_Errors.raise_error uu____32881
              imp.FStar_TypeChecker_Common.imp_range))
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32911 = teq env t1 t2  in
        force_trivial_guard env uu____32911
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32930 = teq_nosmt env t1 t2  in
        match uu____32930 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4517_32949 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4517_32949.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4517_32949.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4517_32949.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4517_32949.FStar_TypeChecker_Common.implicits)
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
        (let uu____32985 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32985
         then
           let uu____32990 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32992 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32990
             uu____32992
         else ());
        (let uu____32997 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32997 with
         | (prob,x,wl) ->
             let g =
               let uu____33016 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____33027  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____33016  in
             ((let uu____33049 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____33049
               then
                 let uu____33054 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____33056 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____33058 =
                   let uu____33060 = FStar_Util.must g  in
                   guard_to_string env uu____33060  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____33054 uu____33056 uu____33058
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
        let uu____33097 = check_subtyping env t1 t2  in
        match uu____33097 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____33116 =
              let uu____33117 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____33117 g  in
            FStar_Pervasives_Native.Some uu____33116
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33136 = check_subtyping env t1 t2  in
        match uu____33136 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____33155 =
              let uu____33156 =
                let uu____33157 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____33157]  in
              FStar_TypeChecker_Env.close_guard env uu____33156 g  in
            FStar_Pervasives_Native.Some uu____33155
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____33195 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____33195
         then
           let uu____33200 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____33202 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____33200
             uu____33202
         else ());
        (let uu____33207 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____33207 with
         | (prob,x,wl) ->
             let g =
               let uu____33222 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____33233  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____33222  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____33258 =
                      let uu____33259 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____33259]  in
                    FStar_TypeChecker_Env.close_guard env uu____33258 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____33300 = subtype_nosmt env t1 t2  in
        match uu____33300 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  