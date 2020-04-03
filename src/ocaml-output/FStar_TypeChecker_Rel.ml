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
         | uu____2318 -> false)
  
let (attempt :
  FStar_TypeChecker_Common.prob Prims.list -> worklist -> worklist) =
  fun probs  ->
    fun wl  ->
      FStar_List.iter (def_check_prob "attempt") probs;
      (let uu___297_2339 = wl  in
       {
         attempting = (FStar_List.append probs wl.attempting);
         wl_deferred = (uu___297_2339.wl_deferred);
         wl_deferred_to_tac = (uu___297_2339.wl_deferred_to_tac);
         ctr = (uu___297_2339.ctr);
         defer_ok = (uu___297_2339.defer_ok);
         smt_ok = (uu___297_2339.smt_ok);
         umax_heuristic_ok = (uu___297_2339.umax_heuristic_ok);
         tcenv = (uu___297_2339.tcenv);
         wl_implicits = (uu___297_2339.wl_implicits)
       })
  
let mk_eq2 :
  'Auu____2353 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2353 ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term -> (FStar_Syntax_Syntax.term * worklist)
  =
  fun wl  ->
    fun env  ->
      fun prob  ->
        fun t1  ->
          fun t2  ->
            let uu____2387 = FStar_Syntax_Util.type_u ()  in
            match uu____2387 with
            | (t_type,u) ->
                let binders = FStar_TypeChecker_Env.all_binders env  in
                let uu____2399 =
                  new_uvar "eq2" wl t1.FStar_Syntax_Syntax.pos
                    env.FStar_TypeChecker_Env.gamma binders t_type
                    FStar_Syntax_Syntax.Allow_unresolved
                    FStar_Pervasives_Native.None
                   in
                (match uu____2399 with
                 | (uu____2411,tt,wl1) ->
                     let uu____2414 = FStar_Syntax_Util.mk_eq2 u tt t1 t2  in
                     (uu____2414, wl1))
  
let (p_invert :
  FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob) =
  fun uu___14_2420  ->
    match uu___14_2420 with
    | FStar_TypeChecker_Common.TProb p ->
        FStar_All.pipe_left
          (fun _2426  -> FStar_TypeChecker_Common.TProb _2426) (invert p)
    | FStar_TypeChecker_Common.CProb p ->
        FStar_All.pipe_left
          (fun _2432  -> FStar_TypeChecker_Common.CProb _2432) (invert p)
  
let (is_top_level_prob : FStar_TypeChecker_Common.prob -> Prims.bool) =
  fun p  ->
    let uu____2440 = FStar_All.pipe_right (p_reason p) FStar_List.length  in
    uu____2440 = Prims.int_one
  
let (next_pid : unit -> Prims.int) =
  let ctr = FStar_Util.mk_ref Prims.int_zero  in
  fun uu____2460  -> FStar_Util.incr ctr; FStar_ST.op_Bang ctr 
let mk_problem :
  'Auu____2502 .
    worklist ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list ->
        FStar_TypeChecker_Common.prob ->
          'Auu____2502 ->
            FStar_TypeChecker_Common.rel ->
              'Auu____2502 ->
                FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                  Prims.string ->
                    ('Auu____2502 FStar_TypeChecker_Common.problem *
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
                        let uu____2589 =
                          let uu____2598 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2598]  in
                        FStar_List.append scope uu____2589
                     in
                  let bs =
                    FStar_List.append
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_binders
                      scope1
                     in
                  let gamma =
                    let uu____2641 =
                      let uu____2644 =
                        FStar_List.map
                          (fun b  ->
                             FStar_Syntax_Syntax.Binding_var
                               (FStar_Pervasives_Native.fst b)) scope1
                         in
                      FStar_List.rev uu____2644  in
                    FStar_List.append uu____2641
                      (p_guard_uvar orig).FStar_Syntax_Syntax.ctx_uvar_gamma
                     in
                  let uu____2663 =
                    new_uvar
                      (Prims.op_Hat "mk_problem: logical guard for " reason)
                      wl FStar_Range.dummyRange gamma bs
                      FStar_Syntax_Util.ktype0
                      FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2663 with
                  | (ctx_uvar,lg,wl1) ->
                      let prob =
                        let uu____2683 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____2683;
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
                  (let uu____2757 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2757 with
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
                  (let uu____2845 =
                     mk_problem wl scope orig lhs rel rhs elt reason  in
                   match uu____2845 with
                   | (p,wl1) ->
                       (def_check_prob (Prims.op_Hat reason ".mk_c")
                          (FStar_TypeChecker_Common.CProb p);
                        ((FStar_TypeChecker_Common.CProb p), wl1)))
  
let new_problem :
  'Auu____2883 .
    worklist ->
      FStar_TypeChecker_Env.env ->
        'Auu____2883 ->
          FStar_TypeChecker_Common.rel ->
            'Auu____2883 ->
              FStar_Syntax_Syntax.bv FStar_Pervasives_Native.option ->
                FStar_Range.range ->
                  Prims.string ->
                    ('Auu____2883 FStar_TypeChecker_Common.problem *
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
                          let uu____2951 = FStar_Syntax_Syntax.mk_binder x
                             in
                          [uu____2951]  in
                        let uu____2970 =
                          FStar_Syntax_Syntax.mk_Total
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_Syntax_Util.arrow bs uu____2970
                     in
                  let uu____2973 =
                    let uu____2980 = FStar_TypeChecker_Env.all_binders env
                       in
                    new_uvar
                      (Prims.op_Hat "new_problem: logical guard for " reason)
                      (let uu___380_2991 = wl  in
                       {
                         attempting = (uu___380_2991.attempting);
                         wl_deferred = (uu___380_2991.wl_deferred);
                         wl_deferred_to_tac =
                           (uu___380_2991.wl_deferred_to_tac);
                         ctr = (uu___380_2991.ctr);
                         defer_ok = (uu___380_2991.defer_ok);
                         smt_ok = (uu___380_2991.smt_ok);
                         umax_heuristic_ok =
                           (uu___380_2991.umax_heuristic_ok);
                         tcenv = env;
                         wl_implicits = (uu___380_2991.wl_implicits)
                       }) loc env.FStar_TypeChecker_Env.gamma uu____2980
                      lg_ty FStar_Syntax_Syntax.Allow_untyped
                      FStar_Pervasives_Native.None
                     in
                  match uu____2973 with
                  | (ctx_uvar,lg,wl1) ->
                      let lg1 =
                        match subject with
                        | FStar_Pervasives_Native.None  -> lg
                        | FStar_Pervasives_Native.Some x ->
                            let uu____3003 =
                              let uu____3008 =
                                let uu____3009 =
                                  let uu____3018 =
                                    FStar_Syntax_Syntax.bv_to_name x  in
                                  FStar_All.pipe_left
                                    FStar_Syntax_Syntax.as_arg uu____3018
                                   in
                                [uu____3009]  in
                              FStar_Syntax_Syntax.mk_Tm_app lg uu____3008  in
                            uu____3003 FStar_Pervasives_Native.None loc
                         in
                      let prob =
                        let uu____3046 = next_pid ()  in
                        {
                          FStar_TypeChecker_Common.pid = uu____3046;
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
                let uu____3094 = next_pid ()  in
                {
                  FStar_TypeChecker_Common.pid = uu____3094;
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
  'Auu____3109 .
    worklist ->
      'Auu____3109 FStar_TypeChecker_Common.problem ->
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
              let uu____3142 =
                let uu____3145 =
                  let uu____3146 =
                    let uu____3153 = FStar_Syntax_Syntax.bv_to_name e  in
                    (x, uu____3153)  in
                  FStar_Syntax_Syntax.NT uu____3146  in
                [uu____3145]  in
              FStar_Syntax_Subst.subst uu____3142 phi
  
let (explain :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> lstring -> Prims.string)
  =
  fun env  ->
    fun d  ->
      fun s  ->
        let uu____3175 =
          (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "ExplainRel"))
            ||
            (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel"))
           in
        if uu____3175
        then
          let uu____3183 =
            FStar_All.pipe_left FStar_Range.string_of_range (p_loc d)  in
          let uu____3186 = prob_to_string env d  in
          let uu____3188 =
            FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>")
             in
          let uu____3195 = FStar_Thunk.force s  in
          FStar_Util.format4
            "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n"
            uu____3183 uu____3186 uu____3188 uu____3195
        else
          (let d1 = maybe_invert_p d  in
           let rel =
             match p_rel d1 with
             | FStar_TypeChecker_Common.EQ  -> "equal to"
             | FStar_TypeChecker_Common.SUB  -> "a subtype of"
             | uu____3207 -> failwith "impossible"  in
           let uu____3210 =
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
           match uu____3210 with
           | (lhs,rhs) ->
               FStar_Util.format3 "%s is not %s the expected type %s" lhs rel
                 rhs)
  
let (commit : uvi Prims.list -> unit) =
  fun uvis  ->
    FStar_All.pipe_right uvis
      (FStar_List.iter
         (fun uu___15_3253  ->
            match uu___15_3253 with
            | UNIV (u,t) ->
                (match t with
                 | FStar_Syntax_Syntax.U_unif u' ->
                     FStar_Syntax_Unionfind.univ_union u u'
                 | uu____3265 -> FStar_Syntax_Unionfind.univ_change u t)
            | TERM (u,t) ->
                ((let uu____3269 =
                    FStar_List.map FStar_Pervasives_Native.fst
                      u.FStar_Syntax_Syntax.ctx_uvar_binders
                     in
                  FStar_TypeChecker_Env.def_check_closed_in
                    t.FStar_Syntax_Syntax.pos "commit" uu____3269 t);
                 FStar_Syntax_Util.set_uvar
                   u.FStar_Syntax_Syntax.ctx_uvar_head t)))
  
let (find_term_uvar :
  FStar_Syntax_Syntax.uvar ->
    uvi Prims.list -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun uv  ->
    fun s  ->
      FStar_Util.find_map s
        (fun uu___16_3300  ->
           match uu___16_3300 with
           | UNIV uu____3303 -> FStar_Pervasives_Native.None
           | TERM (u,t) ->
               let uu____3310 =
                 FStar_Syntax_Unionfind.equiv uv
                   u.FStar_Syntax_Syntax.ctx_uvar_head
                  in
               if uu____3310
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
        (fun uu___17_3338  ->
           match uu___17_3338 with
           | UNIV (u',t) ->
               let uu____3343 = FStar_Syntax_Unionfind.univ_equiv u u'  in
               if uu____3343
               then FStar_Pervasives_Native.Some t
               else FStar_Pervasives_Native.None
           | uu____3350 -> FStar_Pervasives_Native.None)
  
let (whnf' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3362 =
        let uu____3363 =
          let uu____3364 = FStar_Syntax_Util.unmeta t  in
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta;
            FStar_TypeChecker_Env.Reify;
            FStar_TypeChecker_Env.Weak;
            FStar_TypeChecker_Env.HNF] env uu____3364
           in
        FStar_Syntax_Subst.compress uu____3363  in
      FStar_All.pipe_right uu____3362 FStar_Syntax_Util.unlazy_emb
  
let (sn' :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3376 =
        let uu____3377 =
          FStar_TypeChecker_Normalize.normalize
            [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Reify] env t
           in
        FStar_Syntax_Subst.compress uu____3377  in
      FStar_All.pipe_right uu____3376 FStar_Syntax_Util.unlazy_emb
  
let (sn :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3389 =
        let uu____3393 =
          let uu____3395 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3395  in
        FStar_Pervasives_Native.Some uu____3393  in
      FStar_Profiling.profile (fun uu____3398  -> sn' env t) uu____3389
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
          let uu____3423 =
            let uu____3427 =
              let uu____3429 = FStar_TypeChecker_Env.current_module env  in
              FStar_Ident.string_of_lid uu____3429  in
            FStar_Pervasives_Native.Some uu____3427  in
          FStar_Profiling.profile
            (fun uu____3432  ->
               FStar_TypeChecker_Normalize.normalize steps env t) uu____3423
            profiling_tag
  
let (should_strongly_reduce : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____3440 = FStar_Syntax_Util.head_and_args t  in
    match uu____3440 with
    | (h,uu____3459) ->
        let uu____3484 =
          let uu____3485 = FStar_Syntax_Subst.compress h  in
          uu____3485.FStar_Syntax_Syntax.n  in
        (match uu____3484 with
         | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) -> true
         | uu____3490 -> false)
  
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  ->
      let uu____3503 =
        let uu____3507 =
          let uu____3509 = FStar_TypeChecker_Env.current_module env  in
          FStar_Ident.string_of_lid uu____3509  in
        FStar_Pervasives_Native.Some uu____3507  in
      FStar_Profiling.profile
        (fun uu____3514  ->
           let uu____3515 = should_strongly_reduce t  in
           if uu____3515
           then
             let uu____3518 =
               let uu____3519 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta;
                   FStar_TypeChecker_Env.Reify;
                   FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
                   FStar_TypeChecker_Env.UnfoldUntil
                     FStar_Syntax_Syntax.delta_constant] env t
                  in
               FStar_Syntax_Subst.compress uu____3519  in
             FStar_All.pipe_right uu____3518 FStar_Syntax_Util.unlazy_emb
           else whnf' env t) uu____3503 "FStar.TypeChecker.Rel.whnf"
  
let norm_arg :
  'Auu____3530 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term * 'Auu____3530) ->
        (FStar_Syntax_Syntax.term * 'Auu____3530)
  =
  fun env  ->
    fun t  ->
      let uu____3553 = sn env (FStar_Pervasives_Native.fst t)  in
      (uu____3553, (FStar_Pervasives_Native.snd t))
  
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
           (fun uu____3605  ->
              match uu____3605 with
              | (x,imp) ->
                  let uu____3624 =
                    let uu___486_3625 = x  in
                    let uu____3626 = sn env x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___486_3625.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___486_3625.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____3626
                    }  in
                  (uu____3624, imp)))
  
let (norm_univ :
  worklist -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun wl  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____3650 = aux u3  in FStar_Syntax_Syntax.U_succ uu____3650
        | FStar_Syntax_Syntax.U_max us ->
            let uu____3654 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____3654
        | uu____3657 -> u2  in
      let uu____3658 = aux u  in
      FStar_TypeChecker_Normalize.normalize_universe wl.tcenv uu____3658
  
let (normalize_refinement :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  =
  fun steps  ->
    fun env  ->
      fun t0  ->
        let uu____3675 =
          let uu____3679 =
            let uu____3681 = FStar_TypeChecker_Env.current_module env  in
            FStar_Ident.string_of_lid uu____3681  in
          FStar_Pervasives_Native.Some uu____3679  in
        FStar_Profiling.profile
          (fun uu____3684  ->
             FStar_TypeChecker_Normalize.normalize_refinement steps env t0)
          uu____3675 "FStar.TypeChecker.Rel.normalize_refinement"
  
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
                (let uu____3806 = norm_refinement env t12  in
                 match uu____3806 with
                 | {
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine
                       (x1,phi1);
                     FStar_Syntax_Syntax.pos = uu____3821;
                     FStar_Syntax_Syntax.vars = uu____3822;_} ->
                     ((x1.FStar_Syntax_Syntax.sort),
                       (FStar_Pervasives_Native.Some (x1, phi1)))
                 | tt ->
                     let uu____3846 =
                       let uu____3848 = FStar_Syntax_Print.term_to_string tt
                          in
                       let uu____3850 = FStar_Syntax_Print.tag_of_term tt  in
                       FStar_Util.format2 "impossible: Got %s ... %s\n"
                         uu____3848 uu____3850
                        in
                     failwith uu____3846)
          | FStar_Syntax_Syntax.Tm_lazy i ->
              let uu____3866 = FStar_Syntax_Util.unfold_lazy i  in
              aux norm1 uu____3866
          | FStar_Syntax_Syntax.Tm_uinst uu____3867 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3904 =
                   let uu____3905 = FStar_Syntax_Subst.compress t1'  in
                   uu____3905.FStar_Syntax_Syntax.n  in
                 match uu____3904 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3920 -> aux true t1'
                 | uu____3928 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_fvar uu____3943 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____3974 =
                   let uu____3975 = FStar_Syntax_Subst.compress t1'  in
                   uu____3975.FStar_Syntax_Syntax.n  in
                 match uu____3974 with
                 | FStar_Syntax_Syntax.Tm_refine uu____3990 -> aux true t1'
                 | uu____3998 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_app uu____4013 ->
              if norm1
              then (t12, FStar_Pervasives_Native.None)
              else
                (let t1' = norm_refinement env t12  in
                 let uu____4060 =
                   let uu____4061 = FStar_Syntax_Subst.compress t1'  in
                   uu____4061.FStar_Syntax_Syntax.n  in
                 match uu____4060 with
                 | FStar_Syntax_Syntax.Tm_refine uu____4076 -> aux true t1'
                 | uu____4084 -> (t12, FStar_Pervasives_Native.None))
          | FStar_Syntax_Syntax.Tm_type uu____4099 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_constant uu____4114 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_name uu____4129 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_bvar uu____4144 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_arrow uu____4159 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_abs uu____4188 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_quoted uu____4221 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_uvar uu____4242 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_let uu____4269 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_match uu____4297 ->
              (t12, FStar_Pervasives_Native.None)
          | FStar_Syntax_Syntax.Tm_meta uu____4334 ->
              let uu____4341 =
                let uu____4343 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4345 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4343 uu____4345
                 in
              failwith uu____4341
          | FStar_Syntax_Syntax.Tm_ascribed uu____4360 ->
              let uu____4387 =
                let uu____4389 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4391 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4389 uu____4391
                 in
              failwith uu____4387
          | FStar_Syntax_Syntax.Tm_delayed uu____4406 ->
              let uu____4421 =
                let uu____4423 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4425 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4423 uu____4425
                 in
              failwith uu____4421
          | FStar_Syntax_Syntax.Tm_unknown  ->
              let uu____4440 =
                let uu____4442 = FStar_Syntax_Print.term_to_string t12  in
                let uu____4444 = FStar_Syntax_Print.tag_of_term t12  in
                FStar_Util.format2 "impossible (outer): Got %s ... %s\n"
                  uu____4442 uu____4444
                 in
              failwith uu____4440
           in
        let uu____4459 = whnf env t1  in aux false uu____4459
  
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
      let uu____4504 = base_and_refinement env t  in
      FStar_All.pipe_right uu____4504 FStar_Pervasives_Native.fst
  
let (trivial_refinement :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun t  ->
    let uu____4545 = FStar_Syntax_Syntax.null_bv t  in
    (uu____4545, FStar_Syntax_Util.t_true)
  
let (as_refinement :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term))
  =
  fun delta1  ->
    fun env  ->
      fun t  ->
        let uu____4572 = base_and_refinement_maybe_delta delta1 env t  in
        match uu____4572 with
        | (t_base,refinement) ->
            (match refinement with
             | FStar_Pervasives_Native.None  -> trivial_refinement t_base
             | FStar_Pervasives_Native.Some (x,phi) -> (x, phi))
  
let (force_refinement :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)
    FStar_Pervasives_Native.option) -> FStar_Syntax_Syntax.term)
  =
  fun uu____4632  ->
    match uu____4632 with
    | (t_base,refopt) ->
        let uu____4663 =
          match refopt with
          | FStar_Pervasives_Native.Some (y,phi) -> (y, phi)
          | FStar_Pervasives_Native.None  -> trivial_refinement t_base  in
        (match uu____4663 with
         | (y,phi) ->
             FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (y, phi))
               FStar_Pervasives_Native.None t_base.FStar_Syntax_Syntax.pos)
  
let (wl_prob_to_string :
  worklist -> FStar_TypeChecker_Common.prob -> Prims.string) =
  fun wl  -> fun prob  -> prob_to_string wl.tcenv prob 
let (wl_to_string : worklist -> Prims.string) =
  fun wl  ->
    let uu____4705 =
      let uu____4709 =
        let uu____4712 =
          FStar_All.pipe_right wl.wl_deferred
            (FStar_List.map
               (fun uu____4737  ->
                  match uu____4737 with | (uu____4745,uu____4746,x) -> x))
           in
        FStar_List.append wl.attempting uu____4712  in
      FStar_List.map (wl_prob_to_string wl) uu____4709  in
    FStar_All.pipe_right uu____4705 (FStar_String.concat "\n\t")
  
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
  fun uu____4806  ->
    match uu____4806 with
    | Flex (uu____4808,u,uu____4810) -> u.FStar_Syntax_Syntax.ctx_uvar_reason
  
let (flex_t_to_string : flex_t -> Prims.string) =
  fun uu____4817  ->
    match uu____4817 with
    | Flex (uu____4819,c,args) ->
        let uu____4822 = print_ctx_uvar c  in
        let uu____4824 = FStar_Syntax_Print.args_to_string args  in
        FStar_Util.format2 "%s [%s]" uu____4822 uu____4824
  
let (is_flex : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____4834 = FStar_Syntax_Util.head_and_args t  in
    match uu____4834 with
    | (head1,_args) ->
        let uu____4878 =
          let uu____4879 = FStar_Syntax_Subst.compress head1  in
          uu____4879.FStar_Syntax_Syntax.n  in
        (match uu____4878 with
         | FStar_Syntax_Syntax.Tm_uvar uu____4883 -> true
         | uu____4897 -> false)
  
let (flex_uvar_head :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.ctx_uvar) =
  fun t  ->
    let uu____4905 = FStar_Syntax_Util.head_and_args t  in
    match uu____4905 with
    | (head1,_args) ->
        let uu____4948 =
          let uu____4949 = FStar_Syntax_Subst.compress head1  in
          uu____4949.FStar_Syntax_Syntax.n  in
        (match uu____4948 with
         | FStar_Syntax_Syntax.Tm_uvar (u,uu____4953) -> u
         | uu____4970 -> failwith "Not a flex-uvar")
  
let (destruct_flex_t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    worklist -> (flex_t * worklist))
  =
  fun t  ->
    fun wl  ->
      let uu____4995 = FStar_Syntax_Util.head_and_args t  in
      match uu____4995 with
      | (head1,args) ->
          let uu____5042 =
            let uu____5043 = FStar_Syntax_Subst.compress head1  in
            uu____5043.FStar_Syntax_Syntax.n  in
          (match uu____5042 with
           | FStar_Syntax_Syntax.Tm_uvar (uv,([],uu____5051)) ->
               ((Flex (t, uv, args)), wl)
           | FStar_Syntax_Syntax.Tm_uvar (uv,s) ->
               let uu____5084 =
                 FStar_All.pipe_right uv.FStar_Syntax_Syntax.ctx_uvar_gamma
                   (FStar_List.partition
                      (fun uu___18_5109  ->
                         match uu___18_5109 with
                         | FStar_Syntax_Syntax.Binding_var x ->
                             let t_x = FStar_Syntax_Syntax.bv_to_name x  in
                             let t_x' = FStar_Syntax_Subst.subst' s t_x  in
                             let uu____5114 =
                               let uu____5115 =
                                 FStar_Syntax_Subst.compress t_x'  in
                               uu____5115.FStar_Syntax_Syntax.n  in
                             (match uu____5114 with
                              | FStar_Syntax_Syntax.Tm_name y ->
                                  FStar_Syntax_Syntax.bv_eq x y
                              | uu____5120 -> false)
                         | uu____5122 -> true))
                  in
               (match uu____5084 with
                | (new_gamma,dom_binders_rev) ->
                    let dom_binders =
                      let uu____5147 =
                        FStar_List.collect
                          (fun uu___19_5159  ->
                             match uu___19_5159 with
                             | FStar_Syntax_Syntax.Binding_var x ->
                                 let uu____5163 =
                                   FStar_Syntax_Syntax.mk_binder x  in
                                 [uu____5163]
                             | uu____5164 -> []) dom_binders_rev
                         in
                      FStar_All.pipe_right uu____5147 FStar_List.rev  in
                    let uu____5187 =
                      let uu____5194 =
                        let uu____5203 =
                          FStar_All.pipe_right new_gamma
                            (FStar_List.collect
                               (fun uu___20_5225  ->
                                  match uu___20_5225 with
                                  | FStar_Syntax_Syntax.Binding_var x ->
                                      let uu____5229 =
                                        FStar_Syntax_Syntax.mk_binder x  in
                                      [uu____5229]
                                  | uu____5230 -> []))
                           in
                        FStar_All.pipe_right uu____5203 FStar_List.rev  in
                      let uu____5253 =
                        let uu____5256 =
                          FStar_Syntax_Syntax.mk_Total
                            uv.FStar_Syntax_Syntax.ctx_uvar_typ
                           in
                        FStar_Syntax_Util.arrow dom_binders uu____5256  in
                      new_uvar
                        (Prims.op_Hat uv.FStar_Syntax_Syntax.ctx_uvar_reason
                           "; force delayed") wl t.FStar_Syntax_Syntax.pos
                        new_gamma uu____5194 uu____5253
                        uv.FStar_Syntax_Syntax.ctx_uvar_should_check
                        uv.FStar_Syntax_Syntax.ctx_uvar_meta
                       in
                    (match uu____5187 with
                     | (v1,t_v,wl1) ->
                         let args_sol =
                           FStar_List.map
                             (fun uu____5292  ->
                                match uu____5292 with
                                | (x,i) ->
                                    let uu____5311 =
                                      FStar_Syntax_Syntax.bv_to_name x  in
                                    (uu____5311, i)) dom_binders
                            in
                         let sol =
                           FStar_Syntax_Syntax.mk_Tm_app t_v args_sol
                             FStar_Pervasives_Native.None
                             t.FStar_Syntax_Syntax.pos
                            in
                         let args_sol_s =
                           FStar_List.map
                             (fun uu____5342  ->
                                match uu____5342 with
                                | (a,i) ->
                                    let uu____5361 =
                                      FStar_Syntax_Subst.subst' s a  in
                                    (uu____5361, i)) args_sol
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
           | uu____5383 -> failwith "Not a flex-uvar")
  
let (u_abs :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun k  ->
    fun ys  ->
      fun t  ->
        let uu____5405 =
          let uu____5428 =
            let uu____5429 = FStar_Syntax_Subst.compress k  in
            uu____5429.FStar_Syntax_Syntax.n  in
          match uu____5428 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
              if (FStar_List.length bs) = (FStar_List.length ys)
              then
                let uu____5511 = FStar_Syntax_Subst.open_comp bs c  in
                ((ys, t), uu____5511)
              else
                (let uu____5546 = FStar_Syntax_Util.abs_formals t  in
                 match uu____5546 with
                 | (ys',t1,uu____5579) ->
                     let uu____5584 = FStar_Syntax_Util.arrow_formals_comp k
                        in
                     (((FStar_List.append ys ys'), t1), uu____5584))
          | uu____5623 ->
              let uu____5624 =
                let uu____5629 = FStar_Syntax_Syntax.mk_Total k  in
                ([], uu____5629)  in
              ((ys, t), uu____5624)
           in
        match uu____5405 with
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
                 let uu____5724 = FStar_Syntax_Util.rename_binders xs ys1  in
                 FStar_Syntax_Subst.subst_comp uu____5724 c  in
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
               (let uu____5802 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
                    (FStar_Options.Other "Rel")
                   in
                if uu____5802
                then
                  let uu____5807 = FStar_Util.string_of_int (p_pid prob)  in
                  let uu____5809 = print_ctx_uvar uv  in
                  let uu____5811 = FStar_Syntax_Print.term_to_string phi1  in
                  FStar_Util.print3 "Solving %s (%s) with formula %s\n"
                    uu____5807 uu____5809 uu____5811
                else ());
               (let phi2 =
                  FStar_Syntax_Util.abs xs phi1
                    (FStar_Pervasives_Native.Some
                       (FStar_Syntax_Util.residual_tot
                          FStar_Syntax_Util.ktype0))
                   in
                (let uu____5820 =
                   let uu____5822 = FStar_Util.string_of_int (p_pid prob)  in
                   Prims.op_Hat "solve_prob'.sol." uu____5822  in
                 let uu____5825 =
                   let uu____5828 = p_scope prob  in
                   FStar_All.pipe_left
                     (FStar_List.map FStar_Pervasives_Native.fst) uu____5828
                    in
                 FStar_TypeChecker_Env.def_check_closed_in (p_loc prob)
                   uu____5820 uu____5825 phi2);
                FStar_Syntax_Util.set_uvar
                  uv.FStar_Syntax_Syntax.ctx_uvar_head phi2)
                in
             let uv = p_guard_uvar prob  in
             let fail1 uu____5861 =
               let uu____5862 =
                 let uu____5864 = FStar_Syntax_Print.ctx_uvar_to_string uv
                    in
                 let uu____5866 =
                   FStar_Syntax_Print.term_to_string (p_guard prob)  in
                 FStar_Util.format2
                   "Impossible: this instance %s has already been assigned a solution\n%s\n"
                   uu____5864 uu____5866
                  in
               failwith uu____5862  in
             let args_as_binders args =
               FStar_All.pipe_right args
                 (FStar_List.collect
                    (fun uu____5932  ->
                       match uu____5932 with
                       | (a,i) ->
                           let uu____5953 =
                             let uu____5954 = FStar_Syntax_Subst.compress a
                                in
                             uu____5954.FStar_Syntax_Syntax.n  in
                           (match uu____5953 with
                            | FStar_Syntax_Syntax.Tm_name x -> [(x, i)]
                            | uu____5980 -> (fail1 (); []))))
                in
             let wl1 =
               let g = whnf wl.tcenv (p_guard prob)  in
               let uu____5990 =
                 let uu____5992 = is_flex g  in Prims.op_Negation uu____5992
                  in
               if uu____5990
               then (if resolve_ok then wl else (fail1 (); wl))
               else
                 (let uu____6001 = destruct_flex_t g wl  in
                  match uu____6001 with
                  | (Flex (uu____6006,uv1,args),wl1) ->
                      ((let uu____6011 = args_as_binders args  in
                        assign_solution uu____6011 uv1 phi);
                       wl1))
                in
             commit uvis;
             (let uu___748_6013 = wl1  in
              {
                attempting = (uu___748_6013.attempting);
                wl_deferred = (uu___748_6013.wl_deferred);
                wl_deferred_to_tac = (uu___748_6013.wl_deferred_to_tac);
                ctr = (wl1.ctr + Prims.int_one);
                defer_ok = (uu___748_6013.defer_ok);
                smt_ok = (uu___748_6013.smt_ok);
                umax_heuristic_ok = (uu___748_6013.umax_heuristic_ok);
                tcenv = (uu___748_6013.tcenv);
                wl_implicits = (uu___748_6013.wl_implicits)
              }))
  
let (extend_solution : Prims.int -> uvi Prims.list -> worklist -> worklist) =
  fun pid  ->
    fun sol  ->
      fun wl  ->
        (let uu____6038 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
             (FStar_Options.Other "Rel")
            in
         if uu____6038
         then
           let uu____6043 = FStar_Util.string_of_int pid  in
           let uu____6045 =
             let uu____6047 = FStar_List.map (uvi_to_string wl.tcenv) sol  in
             FStar_All.pipe_right uu____6047 (FStar_String.concat ", ")  in
           FStar_Util.print2 "Solving %s: with [%s]\n" uu____6043 uu____6045
         else ());
        commit sol;
        (let uu___756_6061 = wl  in
         {
           attempting = (uu___756_6061.attempting);
           wl_deferred = (uu___756_6061.wl_deferred);
           wl_deferred_to_tac = (uu___756_6061.wl_deferred_to_tac);
           ctr = (wl.ctr + Prims.int_one);
           defer_ok = (uu___756_6061.defer_ok);
           smt_ok = (uu___756_6061.smt_ok);
           umax_heuristic_ok = (uu___756_6061.umax_heuristic_ok);
           tcenv = (uu___756_6061.tcenv);
           wl_implicits = (uu___756_6061.wl_implicits)
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
          (let uu____6097 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv)
               (FStar_Options.Other "Rel")
              in
           if uu____6097
           then
             let uu____6102 =
               FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob)  in
             let uu____6106 =
               let uu____6108 = FStar_List.map (uvi_to_string wl.tcenv) uvis
                  in
               FStar_All.pipe_right uu____6108 (FStar_String.concat ", ")  in
             FStar_Util.print2 "Solving %s: with %s\n" uu____6102 uu____6106
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
        let uu____6143 = FStar_Syntax_Free.uvars t  in
        FStar_All.pipe_right uu____6143 FStar_Util.set_elements  in
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
      let uu____6183 = occurs uk t  in
      match uu____6183 with
      | (uvars1,occurs1) ->
          let msg =
            if Prims.op_Negation occurs1
            then FStar_Pervasives_Native.None
            else
              (let uu____6222 =
                 let uu____6224 =
                   FStar_Syntax_Print.uvar_to_string
                     uk.FStar_Syntax_Syntax.ctx_uvar_head
                    in
                 let uu____6226 = FStar_Syntax_Print.term_to_string t  in
                 FStar_Util.format2 "occurs-check failed (%s occurs in %s)"
                   uu____6224 uu____6226
                  in
               FStar_Pervasives_Native.Some uu____6222)
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
            let uu____6346 = maximal_prefix bs_tail bs'_tail  in
            (match uu____6346 with | (pfx,rest) -> (((b, i) :: pfx), rest))
          else ([], (bs, bs'))
      | uu____6397 -> ([], (bs, bs'))
  
let (extend_gamma :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      FStar_List.fold_left
        (fun g1  ->
           fun uu____6454  ->
             match uu____6454 with
             | (x,uu____6466) -> (FStar_Syntax_Syntax.Binding_var x) :: g1) g
        bs
  
let (gamma_until :
  FStar_Syntax_Syntax.gamma ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binding Prims.list)
  =
  fun g  ->
    fun bs  ->
      let uu____6484 = FStar_List.last bs  in
      match uu____6484 with
      | FStar_Pervasives_Native.None  -> []
      | FStar_Pervasives_Native.Some (x,uu____6508) ->
          let uu____6519 =
            FStar_Util.prefix_until
              (fun uu___21_6534  ->
                 match uu___21_6534 with
                 | FStar_Syntax_Syntax.Binding_var x' ->
                     FStar_Syntax_Syntax.bv_eq x x'
                 | uu____6537 -> false) g
             in
          (match uu____6519 with
           | FStar_Pervasives_Native.None  -> []
           | FStar_Pervasives_Native.Some (uu____6551,bx,rest) -> bx :: rest)
  
let (restrict_ctx :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.ctx_uvar -> worklist -> worklist)
  =
  fun tgt  ->
    fun src  ->
      fun wl  ->
        let uu____6588 =
          maximal_prefix tgt.FStar_Syntax_Syntax.ctx_uvar_binders
            src.FStar_Syntax_Syntax.ctx_uvar_binders
           in
        match uu____6588 with
        | (pfx,uu____6598) ->
            let g = gamma_until src.FStar_Syntax_Syntax.ctx_uvar_gamma pfx
               in
            let uu____6610 =
              new_uvar
                (Prims.op_Hat "restrict:"
                   src.FStar_Syntax_Syntax.ctx_uvar_reason) wl
                src.FStar_Syntax_Syntax.ctx_uvar_range g pfx
                src.FStar_Syntax_Syntax.ctx_uvar_typ
                src.FStar_Syntax_Syntax.ctx_uvar_should_check
                src.FStar_Syntax_Syntax.ctx_uvar_meta
               in
            (match uu____6610 with
             | (uu____6618,src',wl1) ->
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
                 | uu____6732 -> out) FStar_Syntax_Syntax.no_names g
           in
        let uu____6733 =
          FStar_All.pipe_right v2
            (FStar_List.fold_left
               (fun uu____6797  ->
                  fun uu____6798  ->
                    match (uu____6797, uu____6798) with
                    | ((isect,isect_set),(x,imp)) ->
                        let uu____6901 =
                          let uu____6903 = FStar_Util.set_mem x v1_set  in
                          FStar_All.pipe_left Prims.op_Negation uu____6903
                           in
                        if uu____6901
                        then (isect, isect_set)
                        else
                          (let fvs =
                             FStar_Syntax_Free.names
                               x.FStar_Syntax_Syntax.sort
                              in
                           let uu____6937 =
                             FStar_Util.set_is_subset_of fvs isect_set  in
                           if uu____6937
                           then
                             let uu____6954 = FStar_Util.set_add x isect_set
                                in
                             (((x, imp) :: isect), uu____6954)
                           else (isect, isect_set))) ([], ctx_binders))
           in
        match uu____6733 with | (isect,uu____7004) -> FStar_List.rev isect
  
let binders_eq :
  'Auu____7040 'Auu____7041 .
    (FStar_Syntax_Syntax.bv * 'Auu____7040) Prims.list ->
      (FStar_Syntax_Syntax.bv * 'Auu____7041) Prims.list -> Prims.bool
  =
  fun v1  ->
    fun v2  ->
      ((FStar_List.length v1) = (FStar_List.length v2)) &&
        (FStar_List.forall2
           (fun uu____7099  ->
              fun uu____7100  ->
                match (uu____7099, uu____7100) with
                | ((a,uu____7119),(b,uu____7121)) ->
                    FStar_Syntax_Syntax.bv_eq a b) v1 v2)
  
let name_exists_in_binders :
  'Auu____7137 .
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * 'Auu____7137) Prims.list -> Prims.bool
  =
  fun x  ->
    fun bs  ->
      FStar_Util.for_some
        (fun uu____7168  ->
           match uu____7168 with
           | (y,uu____7175) -> FStar_Syntax_Syntax.bv_eq x y) bs
  
let pat_vars :
  'Auu____7185 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____7185) Prims.list ->
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
                   let uu____7347 =
                     (name_exists_in_binders a seen) ||
                       (name_exists_in_binders a ctx)
                      in
                   if uu____7347
                   then FStar_Pervasives_Native.None
                   else aux ((a, i) :: seen) args2
               | uu____7380 -> FStar_Pervasives_Native.None)
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
    match projectee with | MisMatch _0 -> true | uu____7432 -> false
  
let (__proj__MisMatch__item___0 :
  match_result ->
    (FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.delta_depth FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | MisMatch _0 -> _0 
let (uu___is_HeadMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | HeadMatch _0 -> true | uu____7476 -> false
  
let (__proj__HeadMatch__item___0 : match_result -> Prims.bool) =
  fun projectee  -> match projectee with | HeadMatch _0 -> _0 
let (uu___is_FullMatch : match_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | FullMatch  -> true | uu____7497 -> false
  
let (string_of_match_result : match_result -> Prims.string) =
  fun uu___22_7505  ->
    match uu___22_7505 with
    | MisMatch (d1,d2) ->
        let uu____7517 =
          let uu____7519 =
            FStar_Common.string_of_option
              FStar_Syntax_Print.delta_depth_to_string d1
             in
          let uu____7521 =
            let uu____7523 =
              let uu____7525 =
                FStar_Common.string_of_option
                  FStar_Syntax_Print.delta_depth_to_string d2
                 in
              Prims.op_Hat uu____7525 ")"  in
            Prims.op_Hat ") (" uu____7523  in
          Prims.op_Hat uu____7519 uu____7521  in
        Prims.op_Hat "MisMatch (" uu____7517
    | HeadMatch u ->
        let uu____7532 = FStar_Util.string_of_bool u  in
        Prims.op_Hat "HeadMatch " uu____7532
    | FullMatch  -> "FullMatch"
  
let (head_match : match_result -> match_result) =
  fun uu___23_7541  ->
    match uu___23_7541 with
    | MisMatch (i,j) -> MisMatch (i, j)
    | HeadMatch (true ) -> HeadMatch true
    | uu____7558 -> HeadMatch false
  
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
          let uu____7580 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____7580 with
           | FStar_Pervasives_Native.None  ->
               FStar_Syntax_Syntax.delta_constant
           | uu____7591 -> d)
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
      | FStar_Syntax_Syntax.Tm_meta uu____7615 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____7625 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____7644 = FStar_Syntax_Util.unfold_lazy i  in
          delta_depth_of_term env uu____7644
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_bvar uu____7645 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_name uu____7646 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uvar uu____7647 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____7660 -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_match uu____7674 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst (t2,uu____7698) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____7704,uu____7705) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_app (t2,uu____7747) ->
          delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7772;
             FStar_Syntax_Syntax.index = uu____7773;
             FStar_Syntax_Syntax.sort = t2;_},uu____7775)
          -> delta_depth_of_term env t2
      | FStar_Syntax_Syntax.Tm_constant uu____7783 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_type uu____7784 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_arrow uu____7785 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_quoted uu____7800 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_abs uu____7807 ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.delta_constant
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____7827 = fv_delta_depth env fv  in
          FStar_Pervasives_Native.Some uu____7827
  
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
           { FStar_Syntax_Syntax.blob = uu____7846;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7847;
             FStar_Syntax_Syntax.ltyp = uu____7848;
             FStar_Syntax_Syntax.rng = uu____7849;_},uu____7850)
            ->
            let uu____7861 = FStar_Syntax_Util.unlazy t11  in
            head_matches env uu____7861 t21
        | (uu____7862,FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____7863;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____7864;
             FStar_Syntax_Syntax.ltyp = uu____7865;
             FStar_Syntax_Syntax.rng = uu____7866;_})
            ->
            let uu____7877 = FStar_Syntax_Util.unlazy t21  in
            head_matches env t11 uu____7877
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            if FStar_Syntax_Syntax.bv_eq x y
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
            let uu____7889 = FStar_Syntax_Syntax.fv_eq f g  in
            if uu____7889
            then FullMatch
            else
              (let uu____7894 =
                 let uu____7903 =
                   let uu____7906 = fv_delta_depth env f  in
                   FStar_Pervasives_Native.Some uu____7906  in
                 let uu____7907 =
                   let uu____7910 = fv_delta_depth env g  in
                   FStar_Pervasives_Native.Some uu____7910  in
                 (uu____7903, uu____7907)  in
               MisMatch uu____7894)
        | (FStar_Syntax_Syntax.Tm_uinst
           (f,uu____7916),FStar_Syntax_Syntax.Tm_uinst (g,uu____7918)) ->
            let uu____7927 = head_matches env f g  in
            FStar_All.pipe_right uu____7927 head_match
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify )) ->
            FullMatch
        | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
           ),uu____7928) -> HeadMatch true
        | (uu____7930,FStar_Syntax_Syntax.Tm_constant
           (FStar_Const.Const_reify )) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant
           d) ->
            let uu____7934 = FStar_Const.eq_const c d  in
            if uu____7934
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_uvar
           (uv,uu____7944),FStar_Syntax_Syntax.Tm_uvar (uv',uu____7946)) ->
            let uu____7979 =
              FStar_Syntax_Unionfind.equiv
                uv.FStar_Syntax_Syntax.ctx_uvar_head
                uv'.FStar_Syntax_Syntax.ctx_uvar_head
               in
            if uu____7979
            then FullMatch
            else
              MisMatch
                (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
        | (FStar_Syntax_Syntax.Tm_refine
           (x,uu____7989),FStar_Syntax_Syntax.Tm_refine (y,uu____7991)) ->
            let uu____8000 =
              head_matches env x.FStar_Syntax_Syntax.sort
                y.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8000 head_match
        | (FStar_Syntax_Syntax.Tm_refine (x,uu____8002),uu____8003) ->
            let uu____8008 = head_matches env x.FStar_Syntax_Syntax.sort t21
               in
            FStar_All.pipe_right uu____8008 head_match
        | (uu____8009,FStar_Syntax_Syntax.Tm_refine (x,uu____8011)) ->
            let uu____8016 = head_matches env t11 x.FStar_Syntax_Syntax.sort
               in
            FStar_All.pipe_right uu____8016 head_match
        | (FStar_Syntax_Syntax.Tm_type uu____8017,FStar_Syntax_Syntax.Tm_type
           uu____8018) -> HeadMatch false
        | (FStar_Syntax_Syntax.Tm_arrow
           uu____8020,FStar_Syntax_Syntax.Tm_arrow uu____8021) ->
            HeadMatch false
        | (FStar_Syntax_Syntax.Tm_app
           (head1,uu____8052),FStar_Syntax_Syntax.Tm_app (head',uu____8054))
            ->
            let uu____8103 = head_matches env head1 head'  in
            FStar_All.pipe_right uu____8103 head_match
        | (FStar_Syntax_Syntax.Tm_app (head1,uu____8105),uu____8106) ->
            let uu____8131 = head_matches env head1 t21  in
            FStar_All.pipe_right uu____8131 head_match
        | (uu____8132,FStar_Syntax_Syntax.Tm_app (head1,uu____8134)) ->
            let uu____8159 = head_matches env t11 head1  in
            FStar_All.pipe_right uu____8159 head_match
        | (FStar_Syntax_Syntax.Tm_let uu____8160,FStar_Syntax_Syntax.Tm_let
           uu____8161) -> HeadMatch true
        | (FStar_Syntax_Syntax.Tm_match
           uu____8189,FStar_Syntax_Syntax.Tm_match uu____8190) ->
            HeadMatch true
        | (FStar_Syntax_Syntax.Tm_abs uu____8236,FStar_Syntax_Syntax.Tm_abs
           uu____8237) -> HeadMatch true
        | uu____8275 ->
            let uu____8280 =
              let uu____8289 = delta_depth_of_term env t11  in
              let uu____8292 = delta_depth_of_term env t21  in
              (uu____8289, uu____8292)  in
            MisMatch uu____8280
  
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
              let uu____8361 = unrefine env t  in
              FStar_Syntax_Util.head_of uu____8361  in
            (let uu____8363 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8363
             then
               let uu____8368 = FStar_Syntax_Print.term_to_string t  in
               let uu____8370 = FStar_Syntax_Print.term_to_string head1  in
               FStar_Util.print2 "Head of %s is %s\n" uu____8368 uu____8370
             else ());
            (let uu____8375 =
               let uu____8376 = FStar_Syntax_Util.un_uinst head1  in
               uu____8376.FStar_Syntax_Syntax.n  in
             match uu____8375 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____8382 =
                   FStar_TypeChecker_Env.lookup_definition
                     [FStar_TypeChecker_Env.Unfold
                        FStar_Syntax_Syntax.delta_constant;
                     FStar_TypeChecker_Env.Eager_unfolding_only] env
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                    in
                 (match uu____8382 with
                  | FStar_Pervasives_Native.None  ->
                      ((let uu____8396 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "RelDelta")
                           in
                        if uu____8396
                        then
                          let uu____8401 =
                            FStar_Syntax_Print.term_to_string head1  in
                          FStar_Util.print1 "No definition found for %s\n"
                            uu____8401
                        else ());
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.Some uu____8406 ->
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
                      let uu____8424 =
                        let uu____8426 = FStar_Syntax_Util.eq_tm t t'  in
                        uu____8426 = FStar_Syntax_Util.Equal  in
                      if uu____8424
                      then FStar_Pervasives_Native.None
                      else
                        ((let uu____8433 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelDelta")
                             in
                          if uu____8433
                          then
                            let uu____8438 =
                              FStar_Syntax_Print.term_to_string t  in
                            let uu____8440 =
                              FStar_Syntax_Print.term_to_string t'  in
                            FStar_Util.print2 "Inlined %s to %s\n" uu____8438
                              uu____8440
                          else ());
                         FStar_Pervasives_Native.Some t'))
             | uu____8445 -> FStar_Pervasives_Native.None)
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
            (let uu____8597 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "RelDelta")
                in
             if uu____8597
             then
               let uu____8602 = FStar_Syntax_Print.term_to_string t11  in
               let uu____8604 = FStar_Syntax_Print.term_to_string t21  in
               let uu____8606 = string_of_match_result r  in
               FStar_Util.print3 "head_matches (%s, %s) = %s\n" uu____8602
                 uu____8604 uu____8606
             else ());
            (let reduce_one_and_try_again d1 d2 =
               let d1_greater_than_d2 =
                 FStar_TypeChecker_Common.delta_depth_greater_than d1 d2  in
               let uu____8634 =
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
               match uu____8634 with
               | (t12,t22) -> aux retry1 (n_delta + Prims.int_one) t12 t22
                in
             let reduce_both_and_try_again d r1 =
               let uu____8682 = FStar_TypeChecker_Common.decr_delta_depth d
                  in
               match uu____8682 with
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
                  uu____8720),uu____8721)
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8742 =
                      let uu____8751 = maybe_inline t11  in
                      let uu____8754 = maybe_inline t21  in
                      (uu____8751, uu____8754)  in
                    match uu____8742 with
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
                 (uu____8797,FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Delta_equational_at_level uu____8798))
                 ->
                 if Prims.op_Negation retry1
                 then fail1 n_delta r t11 t21
                 else
                   (let uu____8819 =
                      let uu____8828 = maybe_inline t11  in
                      let uu____8831 = maybe_inline t21  in
                      (uu____8828, uu____8831)  in
                    match uu____8819 with
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
             | MisMatch uu____8886 -> fail1 n_delta r t11 t21
             | uu____8895 -> success n_delta r t11 t21)
             in
          let r = aux true Prims.int_zero t1 t2  in
          (let uu____8910 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "RelDelta")
              in
           if uu____8910
           then
             let uu____8915 = FStar_Syntax_Print.term_to_string t1  in
             let uu____8917 = FStar_Syntax_Print.term_to_string t2  in
             let uu____8919 =
               string_of_match_result (FStar_Pervasives_Native.fst r)  in
             let uu____8927 =
               if FStar_Option.isNone (FStar_Pervasives_Native.snd r)
               then "None"
               else
                 (let uu____8944 =
                    FStar_All.pipe_right (FStar_Pervasives_Native.snd r)
                      FStar_Util.must
                     in
                  FStar_All.pipe_right uu____8944
                    (fun uu____8979  ->
                       match uu____8979 with
                       | (t11,t21) ->
                           let uu____8987 =
                             FStar_Syntax_Print.term_to_string t11  in
                           let uu____8989 =
                             let uu____8991 =
                               FStar_Syntax_Print.term_to_string t21  in
                             Prims.op_Hat "; " uu____8991  in
                           Prims.op_Hat uu____8987 uu____8989))
                in
             FStar_Util.print4 "head_matches_delta (%s, %s) = %s (%s)\n"
               uu____8915 uu____8917 uu____8919 uu____8927
           else ());
          r
  
let (kind_type :
  FStar_Syntax_Syntax.binders -> FStar_Range.range -> FStar_Syntax_Syntax.typ)
  =
  fun binders  ->
    fun r  ->
      let uu____9008 = FStar_Syntax_Util.type_u ()  in
      FStar_All.pipe_right uu____9008 FStar_Pervasives_Native.fst
  
let (rank_t_num : FStar_TypeChecker_Common.rank_t -> Prims.int) =
  fun uu___24_9023  ->
    match uu___24_9023 with
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
      let uu___1245_9072 = p  in
      let uu____9075 = whnf tcenv p.FStar_TypeChecker_Common.lhs  in
      let uu____9076 = whnf tcenv p.FStar_TypeChecker_Common.rhs  in
      {
        FStar_TypeChecker_Common.pid =
          (uu___1245_9072.FStar_TypeChecker_Common.pid);
        FStar_TypeChecker_Common.lhs = uu____9075;
        FStar_TypeChecker_Common.relation =
          (uu___1245_9072.FStar_TypeChecker_Common.relation);
        FStar_TypeChecker_Common.rhs = uu____9076;
        FStar_TypeChecker_Common.element =
          (uu___1245_9072.FStar_TypeChecker_Common.element);
        FStar_TypeChecker_Common.logical_guard =
          (uu___1245_9072.FStar_TypeChecker_Common.logical_guard);
        FStar_TypeChecker_Common.logical_guard_uvar =
          (uu___1245_9072.FStar_TypeChecker_Common.logical_guard_uvar);
        FStar_TypeChecker_Common.reason =
          (uu___1245_9072.FStar_TypeChecker_Common.reason);
        FStar_TypeChecker_Common.loc =
          (uu___1245_9072.FStar_TypeChecker_Common.loc);
        FStar_TypeChecker_Common.rank =
          (uu___1245_9072.FStar_TypeChecker_Common.rank)
      }
  
let (compress_prob :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob -> FStar_TypeChecker_Common.prob)
  =
  fun tcenv  ->
    fun p  ->
      match p with
      | FStar_TypeChecker_Common.TProb p1 ->
          let uu____9091 = compress_tprob tcenv p1  in
          FStar_All.pipe_right uu____9091
            (fun _9096  -> FStar_TypeChecker_Common.TProb _9096)
      | FStar_TypeChecker_Common.CProb uu____9097 -> p
  
let (rank :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.prob ->
      (FStar_TypeChecker_Common.rank_t * FStar_TypeChecker_Common.prob))
  =
  fun tcenv  ->
    fun pr  ->
      let prob =
        let uu____9120 = compress_prob tcenv pr  in
        FStar_All.pipe_right uu____9120 maybe_invert_p  in
      match prob with
      | FStar_TypeChecker_Common.TProb tp ->
          let uu____9128 =
            FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs
             in
          (match uu____9128 with
           | (lh,lhs_args) ->
               let uu____9175 =
                 FStar_Syntax_Util.head_and_args
                   tp.FStar_TypeChecker_Common.rhs
                  in
               (match uu____9175 with
                | (rh,rhs_args) ->
                    let uu____9222 =
                      match ((lh.FStar_Syntax_Syntax.n),
                              (rh.FStar_Syntax_Syntax.n))
                      with
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9235,FStar_Syntax_Syntax.Tm_uvar uu____9236)
                          ->
                          (match (lhs_args, rhs_args) with
                           | ([],[]) when
                               tp.FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ
                               ->
                               (FStar_TypeChecker_Common.Flex_flex_pattern_eq,
                                 tp)
                           | uu____9325 ->
                               (FStar_TypeChecker_Common.Flex_flex, tp))
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9352,uu____9353)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (uu____9368,FStar_Syntax_Syntax.Tm_uvar uu____9369)
                          when
                          tp.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                          -> (FStar_TypeChecker_Common.Flex_rigid_eq, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9384,FStar_Syntax_Syntax.Tm_arrow uu____9385)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1296_9415 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1296_9415.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1296_9415.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1296_9415.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1296_9415.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1296_9415.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1296_9415.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1296_9415.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1296_9415.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1296_9415.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_uvar
                         uu____9418,FStar_Syntax_Syntax.Tm_type uu____9419)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1296_9435 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1296_9435.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1296_9435.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1296_9435.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1296_9435.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1296_9435.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1296_9435.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1296_9435.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1296_9435.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1296_9435.FStar_TypeChecker_Common.rank)
                             }))
                      | (FStar_Syntax_Syntax.Tm_type
                         uu____9438,FStar_Syntax_Syntax.Tm_uvar uu____9439)
                          ->
                          (FStar_TypeChecker_Common.Flex_rigid_eq,
                            (let uu___1296_9455 = tp  in
                             {
                               FStar_TypeChecker_Common.pid =
                                 (uu___1296_9455.FStar_TypeChecker_Common.pid);
                               FStar_TypeChecker_Common.lhs =
                                 (uu___1296_9455.FStar_TypeChecker_Common.lhs);
                               FStar_TypeChecker_Common.relation =
                                 FStar_TypeChecker_Common.EQ;
                               FStar_TypeChecker_Common.rhs =
                                 (uu___1296_9455.FStar_TypeChecker_Common.rhs);
                               FStar_TypeChecker_Common.element =
                                 (uu___1296_9455.FStar_TypeChecker_Common.element);
                               FStar_TypeChecker_Common.logical_guard =
                                 (uu___1296_9455.FStar_TypeChecker_Common.logical_guard);
                               FStar_TypeChecker_Common.logical_guard_uvar =
                                 (uu___1296_9455.FStar_TypeChecker_Common.logical_guard_uvar);
                               FStar_TypeChecker_Common.reason =
                                 (uu___1296_9455.FStar_TypeChecker_Common.reason);
                               FStar_TypeChecker_Common.loc =
                                 (uu___1296_9455.FStar_TypeChecker_Common.loc);
                               FStar_TypeChecker_Common.rank =
                                 (uu___1296_9455.FStar_TypeChecker_Common.rank)
                             }))
                      | (uu____9458,FStar_Syntax_Syntax.Tm_uvar uu____9459)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (FStar_Syntax_Syntax.Tm_uvar uu____9474,uu____9475)
                          -> (FStar_TypeChecker_Common.Flex_rigid, tp)
                      | (uu____9490,FStar_Syntax_Syntax.Tm_uvar uu____9491)
                          -> (FStar_TypeChecker_Common.Rigid_flex, tp)
                      | (uu____9506,uu____9507) ->
                          (FStar_TypeChecker_Common.Rigid_rigid, tp)
                       in
                    (match uu____9222 with
                     | (rank,tp1) ->
                         let uu____9520 =
                           FStar_All.pipe_right
                             (let uu___1316_9524 = tp1  in
                              {
                                FStar_TypeChecker_Common.pid =
                                  (uu___1316_9524.FStar_TypeChecker_Common.pid);
                                FStar_TypeChecker_Common.lhs =
                                  (uu___1316_9524.FStar_TypeChecker_Common.lhs);
                                FStar_TypeChecker_Common.relation =
                                  (uu___1316_9524.FStar_TypeChecker_Common.relation);
                                FStar_TypeChecker_Common.rhs =
                                  (uu___1316_9524.FStar_TypeChecker_Common.rhs);
                                FStar_TypeChecker_Common.element =
                                  (uu___1316_9524.FStar_TypeChecker_Common.element);
                                FStar_TypeChecker_Common.logical_guard =
                                  (uu___1316_9524.FStar_TypeChecker_Common.logical_guard);
                                FStar_TypeChecker_Common.logical_guard_uvar =
                                  (uu___1316_9524.FStar_TypeChecker_Common.logical_guard_uvar);
                                FStar_TypeChecker_Common.reason =
                                  (uu___1316_9524.FStar_TypeChecker_Common.reason);
                                FStar_TypeChecker_Common.loc =
                                  (uu___1316_9524.FStar_TypeChecker_Common.loc);
                                FStar_TypeChecker_Common.rank =
                                  (FStar_Pervasives_Native.Some rank)
                              })
                             (fun _9527  ->
                                FStar_TypeChecker_Common.TProb _9527)
                            in
                         (rank, uu____9520))))
      | FStar_TypeChecker_Common.CProb cp ->
          let uu____9531 =
            FStar_All.pipe_right
              (let uu___1320_9535 = cp  in
               {
                 FStar_TypeChecker_Common.pid =
                   (uu___1320_9535.FStar_TypeChecker_Common.pid);
                 FStar_TypeChecker_Common.lhs =
                   (uu___1320_9535.FStar_TypeChecker_Common.lhs);
                 FStar_TypeChecker_Common.relation =
                   (uu___1320_9535.FStar_TypeChecker_Common.relation);
                 FStar_TypeChecker_Common.rhs =
                   (uu___1320_9535.FStar_TypeChecker_Common.rhs);
                 FStar_TypeChecker_Common.element =
                   (uu___1320_9535.FStar_TypeChecker_Common.element);
                 FStar_TypeChecker_Common.logical_guard =
                   (uu___1320_9535.FStar_TypeChecker_Common.logical_guard);
                 FStar_TypeChecker_Common.logical_guard_uvar =
                   (uu___1320_9535.FStar_TypeChecker_Common.logical_guard_uvar);
                 FStar_TypeChecker_Common.reason =
                   (uu___1320_9535.FStar_TypeChecker_Common.reason);
                 FStar_TypeChecker_Common.loc =
                   (uu___1320_9535.FStar_TypeChecker_Common.loc);
                 FStar_TypeChecker_Common.rank =
                   (FStar_Pervasives_Native.Some
                      FStar_TypeChecker_Common.Rigid_rigid)
               }) (fun _9538  -> FStar_TypeChecker_Common.CProb _9538)
             in
          (FStar_TypeChecker_Common.Rigid_rigid, uu____9531)
  
let (next_prob :
  worklist ->
    (FStar_TypeChecker_Common.prob * FStar_TypeChecker_Common.prob Prims.list
      * FStar_TypeChecker_Common.rank_t) FStar_Pervasives_Native.option)
  =
  fun wl  ->
    let rec aux uu____9598 probs =
      match uu____9598 with
      | (min_rank,min1,out) ->
          (match probs with
           | [] ->
               (match (min1, min_rank) with
                | (FStar_Pervasives_Native.Some
                   p,FStar_Pervasives_Native.Some r) ->
                    FStar_Pervasives_Native.Some (p, out, r)
                | uu____9679 -> FStar_Pervasives_Native.None)
           | hd1::tl1 ->
               let uu____9700 = rank wl.tcenv hd1  in
               (match uu____9700 with
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
                      (let uu____9761 =
                         (min_rank = FStar_Pervasives_Native.None) ||
                           (let uu____9766 = FStar_Option.get min_rank  in
                            rank_less_than rank1 uu____9766)
                          in
                       if uu____9761
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
          let uu____9839 = FStar_Syntax_Util.head_and_args t  in
          match uu____9839 with
          | (hd1,uu____9858) ->
              let uu____9883 =
                let uu____9884 = FStar_Syntax_Subst.compress hd1  in
                uu____9884.FStar_Syntax_Syntax.n  in
              (match uu____9883 with
               | FStar_Syntax_Syntax.Tm_uvar (u,uu____9889) ->
                   FStar_All.pipe_right
                     u.FStar_Syntax_Syntax.ctx_uvar_binders
                     (FStar_Util.for_some
                        (fun uu____9924  ->
                           match uu____9924 with
                           | (y,uu____9933) ->
                               FStar_All.pipe_right bs
                                 (FStar_Util.for_some
                                    (fun uu____9956  ->
                                       match uu____9956 with
                                       | (x,uu____9965) ->
                                           FStar_Syntax_Syntax.bv_eq x y))))
               | uu____9970 -> false)
           in
        let uu____9972 = rank tcenv p  in
        match uu____9972 with
        | (r,p1) ->
            (match p1 with
             | FStar_TypeChecker_Common.CProb uu____9981 -> true
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
    match projectee with | UDeferred _0 -> true | uu____10062 -> false
  
let (__proj__UDeferred__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | UDeferred _0 -> _0 
let (uu___is_USolved : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | USolved _0 -> true | uu____10081 -> false
  
let (__proj__USolved__item___0 : univ_eq_sol -> worklist) =
  fun projectee  -> match projectee with | USolved _0 -> _0 
let (uu___is_UFailed : univ_eq_sol -> Prims.bool) =
  fun projectee  ->
    match projectee with | UFailed _0 -> true | uu____10100 -> false
  
let (__proj__UFailed__item___0 : univ_eq_sol -> lstring) =
  fun projectee  -> match projectee with | UFailed _0 -> _0 
let (ufailed_simple : Prims.string -> univ_eq_sol) =
  fun s  -> let uu____10117 = FStar_Thunk.mkv s  in UFailed uu____10117 
let (ufailed_thunk : (unit -> Prims.string) -> univ_eq_sol) =
  fun s  -> let uu____10132 = FStar_Thunk.mk s  in UFailed uu____10132 
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
                        let uu____10184 = FStar_Syntax_Util.univ_kernel u3
                           in
                        match uu____10184 with
                        | (k,uu____10192) ->
                            (match k with
                             | FStar_Syntax_Syntax.U_unif v2 ->
                                 FStar_Syntax_Unionfind.univ_equiv v1 v2
                             | uu____10205 -> false)))
            | uu____10207 -> occurs_univ v1 (FStar_Syntax_Syntax.U_max [u])
             in
          let rec filter_out_common_univs u12 u22 =
            let common_elts =
              FStar_All.pipe_right u12
                (FStar_List.fold_left
                   (fun uvs  ->
                      fun uv1  ->
                        let uu____10259 =
                          FStar_All.pipe_right u22
                            (FStar_List.existsML
                               (fun uv2  ->
                                  let uu____10267 =
                                    FStar_Syntax_Util.compare_univs uv1 uv2
                                     in
                                  uu____10267 = Prims.int_zero))
                           in
                        if uu____10259 then uv1 :: uvs else uvs) [])
               in
            let filter1 =
              FStar_List.filter
                (fun u  ->
                   let uu____10288 =
                     FStar_All.pipe_right common_elts
                       (FStar_List.existsML
                          (fun u'  ->
                             let uu____10296 =
                               FStar_Syntax_Util.compare_univs u u'  in
                             uu____10296 = Prims.int_zero))
                      in
                   Prims.op_Negation uu____10288)
               in
            let uu____10300 = filter1 u12  in
            let uu____10303 = filter1 u22  in (uu____10300, uu____10303)  in
          let try_umax_components u12 u22 msg =
            if Prims.op_Negation wl.umax_heuristic_ok
            then ufailed_simple "Unable to unify universe terms with umax"
            else
              (match (u12, u22) with
               | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max
                  us2) ->
                   let uu____10338 = filter_out_common_univs us1 us2  in
                   (match uu____10338 with
                    | (us11,us21) ->
                        if
                          (FStar_List.length us11) = (FStar_List.length us21)
                        then
                          let rec aux wl1 us12 us22 =
                            match (us12, us22) with
                            | (u13::us13,u23::us23) ->
                                let uu____10398 =
                                  really_solve_universe_eq pid_orig wl1 u13
                                    u23
                                   in
                                (match uu____10398 with
                                 | USolved wl2 -> aux wl2 us13 us23
                                 | failed -> failed)
                            | uu____10401 -> USolved wl1  in
                          aux wl us11 us21
                        else
                          ufailed_thunk
                            (fun uu____10418  ->
                               let uu____10419 =
                                 FStar_Syntax_Print.univ_to_string u12  in
                               let uu____10421 =
                                 FStar_Syntax_Print.univ_to_string u22  in
                               FStar_Util.format2
                                 "Unable to unify universes: %s and %s"
                                 uu____10419 uu____10421))
               | (FStar_Syntax_Syntax.U_max us,u') ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10447 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10447 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | (u',FStar_Syntax_Syntax.U_max us) ->
                   let rec aux wl1 us1 =
                     match us1 with
                     | [] -> USolved wl1
                     | u::us2 ->
                         let uu____10473 =
                           really_solve_universe_eq pid_orig wl1 u u'  in
                         (match uu____10473 with
                          | USolved wl2 -> aux wl2 us2
                          | failed -> failed)
                      in
                   aux wl us
               | uu____10476 ->
                   ufailed_thunk
                     (fun uu____10487  ->
                        let uu____10488 =
                          FStar_Syntax_Print.univ_to_string u12  in
                        let uu____10490 =
                          FStar_Syntax_Print.univ_to_string u22  in
                        FStar_Util.format3
                          "Unable to unify universes: %s and %s (%s)"
                          uu____10488 uu____10490 msg))
             in
          match (u11, u21) with
          | (FStar_Syntax_Syntax.U_bvar uu____10493,uu____10494) ->
              let uu____10496 =
                let uu____10498 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10500 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10498 uu____10500
                 in
              failwith uu____10496
          | (FStar_Syntax_Syntax.U_unknown ,uu____10503) ->
              let uu____10504 =
                let uu____10506 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10508 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10506 uu____10508
                 in
              failwith uu____10504
          | (uu____10511,FStar_Syntax_Syntax.U_bvar uu____10512) ->
              let uu____10514 =
                let uu____10516 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10518 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10516 uu____10518
                 in
              failwith uu____10514
          | (uu____10521,FStar_Syntax_Syntax.U_unknown ) ->
              let uu____10522 =
                let uu____10524 = FStar_Syntax_Print.univ_to_string u11  in
                let uu____10526 = FStar_Syntax_Print.univ_to_string u21  in
                FStar_Util.format2
                  "Impossible: found an de Bruijn universe variable or unknown universe: %s, %s"
                  uu____10524 uu____10526
                 in
              failwith uu____10522
          | (FStar_Syntax_Syntax.U_name x,FStar_Syntax_Syntax.U_name y) ->
              if x.FStar_Ident.idText = y.FStar_Ident.idText
              then USolved wl
              else ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
              USolved wl
          | (FStar_Syntax_Syntax.U_succ u12,FStar_Syntax_Syntax.U_succ u22)
              -> really_solve_universe_eq pid_orig wl u12 u22
          | (FStar_Syntax_Syntax.U_unif v1,FStar_Syntax_Syntax.U_unif v2) ->
              let uu____10556 = FStar_Syntax_Unionfind.univ_equiv v1 v2  in
              if uu____10556
              then USolved wl
              else
                (let wl1 = extend_solution pid_orig [UNIV (v1, u21)] wl  in
                 USolved wl1)
          | (FStar_Syntax_Syntax.U_unif v1,u) ->
              let u3 = norm_univ wl u  in
              let uu____10573 = occurs_univ v1 u3  in
              if uu____10573
              then
                let uu____10576 =
                  let uu____10578 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10580 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10578 uu____10580
                   in
                try_umax_components u11 u21 uu____10576
              else
                (let uu____10585 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10585)
          | (u,FStar_Syntax_Syntax.U_unif v1) ->
              let u3 = norm_univ wl u  in
              let uu____10597 = occurs_univ v1 u3  in
              if uu____10597
              then
                let uu____10600 =
                  let uu____10602 =
                    FStar_Syntax_Print.univ_to_string
                      (FStar_Syntax_Syntax.U_unif v1)
                     in
                  let uu____10604 = FStar_Syntax_Print.univ_to_string u3  in
                  FStar_Util.format2 "Failed occurs check: %s occurs in %s"
                    uu____10602 uu____10604
                   in
                try_umax_components u11 u21 uu____10600
              else
                (let uu____10609 =
                   extend_solution pid_orig [UNIV (v1, u3)] wl  in
                 USolved uu____10609)
          | (FStar_Syntax_Syntax.U_max uu____10610,uu____10611) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10619 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10619
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (uu____10625,FStar_Syntax_Syntax.U_max uu____10626) ->
              if wl.defer_ok
              then UDeferred wl
              else
                (let u12 = norm_univ wl u11  in
                 let u22 = norm_univ wl u21  in
                 let uu____10634 = FStar_Syntax_Util.eq_univs u12 u22  in
                 if uu____10634
                 then USolved wl
                 else try_umax_components u12 u22 "")
          | (FStar_Syntax_Syntax.U_succ
             uu____10640,FStar_Syntax_Syntax.U_zero ) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_succ
             uu____10642,FStar_Syntax_Syntax.U_name uu____10643) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_succ
             uu____10645) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_name
             uu____10647) -> ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10649,FStar_Syntax_Syntax.U_succ uu____10650) ->
              ufailed_simple "Incompatible universes"
          | (FStar_Syntax_Syntax.U_name
             uu____10652,FStar_Syntax_Syntax.U_zero ) ->
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
      let uu____10759 = bc1  in
      match uu____10759 with
      | (bs1,mk_cod1) ->
          let uu____10803 = bc2  in
          (match uu____10803 with
           | (bs2,mk_cod2) ->
               let rec aux bs11 bs21 =
                 match (bs11, bs21) with
                 | (x::xs,y::ys) ->
                     let uu____10914 = aux xs ys  in
                     (match uu____10914 with
                      | ((xs1,xr),(ys1,yr)) ->
                          (((x :: xs1), xr), ((y :: ys1), yr)))
                 | (xs,ys) ->
                     let uu____10997 =
                       let uu____11004 = mk_cod1 xs  in ([], uu____11004)  in
                     let uu____11007 =
                       let uu____11014 = mk_cod2 ys  in ([], uu____11014)  in
                     (uu____10997, uu____11007)
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
                  let uu____11083 = FStar_Syntax_Syntax.bv_to_name t  in
                  FStar_Syntax_Util.mk_has_type t11 uu____11083 t21
              | FStar_Pervasives_Native.None  ->
                  let x =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      t11
                     in
                  let u_x = env.FStar_TypeChecker_Env.universe_of env t11  in
                  let uu____11086 =
                    let uu____11087 = FStar_Syntax_Syntax.bv_to_name x  in
                    FStar_Syntax_Util.mk_has_type t11 uu____11087 t21  in
                  FStar_Syntax_Util.mk_forall u_x x uu____11086
               in
            match problem.FStar_TypeChecker_Common.relation with
            | FStar_TypeChecker_Common.EQ  ->
                mk_eq2 wl env (FStar_TypeChecker_Common.TProb problem) t1 t2
            | FStar_TypeChecker_Common.SUB  ->
                let uu____11092 = has_type_guard t1 t2  in (uu____11092, wl)
            | FStar_TypeChecker_Common.SUBINV  ->
                let uu____11093 = has_type_guard t2 t1  in (uu____11093, wl)
  
let (is_flex_pat : flex_t -> Prims.bool) =
  fun uu___25_11100  ->
    match uu___25_11100 with
    | Flex (uu____11102,uu____11103,[]) -> true
    | uu____11113 -> false
  
let (should_defer_flex_to_user_tac : worklist -> flex_t -> Prims.bool) =
  fun wl  ->
    fun f  ->
      let uu____11127 = f  in
      match uu____11127 with
      | Flex (uu____11129,u,uu____11131) ->
          should_defer_uvar_to_user_tac wl.tcenv u
  
let (quasi_pattern :
  FStar_TypeChecker_Env.env ->
    flex_t ->
      (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.typ)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun f  ->
      let uu____11155 = f  in
      match uu____11155 with
      | Flex
          (uu____11162,{ FStar_Syntax_Syntax.ctx_uvar_head = uu____11163;
                         FStar_Syntax_Syntax.ctx_uvar_gamma = uu____11164;
                         FStar_Syntax_Syntax.ctx_uvar_binders = ctx;
                         FStar_Syntax_Syntax.ctx_uvar_typ = t_hd;
                         FStar_Syntax_Syntax.ctx_uvar_reason = uu____11167;
                         FStar_Syntax_Syntax.ctx_uvar_should_check =
                           uu____11168;
                         FStar_Syntax_Syntax.ctx_uvar_range = uu____11169;
                         FStar_Syntax_Syntax.ctx_uvar_meta = uu____11170;_},args)
          ->
          let name_exists_in x bs =
            FStar_Util.for_some
              (fun uu____11234  ->
                 match uu____11234 with
                 | (y,uu____11243) -> FStar_Syntax_Syntax.bv_eq x y) bs
             in
          let rec aux pat_binders formals t_res args1 =
            match (formals, args1) with
            | ([],[]) ->
                let uu____11397 =
                  let uu____11412 =
                    let uu____11415 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11415  in
                  ((FStar_List.rev pat_binders), uu____11412)  in
                FStar_Pervasives_Native.Some uu____11397
            | (uu____11448,[]) ->
                let uu____11479 =
                  let uu____11494 =
                    let uu____11497 = FStar_Syntax_Syntax.mk_Total t_res  in
                    FStar_Syntax_Util.arrow formals uu____11497  in
                  ((FStar_List.rev pat_binders), uu____11494)  in
                FStar_Pervasives_Native.Some uu____11479
            | ((formal,formal_imp)::formals1,(a,a_imp)::args2) ->
                let uu____11588 =
                  let uu____11589 = FStar_Syntax_Subst.compress a  in
                  uu____11589.FStar_Syntax_Syntax.n  in
                (match uu____11588 with
                 | FStar_Syntax_Syntax.Tm_name x ->
                     let uu____11609 =
                       (name_exists_in x ctx) ||
                         (name_exists_in x pat_binders)
                        in
                     if uu____11609
                     then
                       aux ((formal, formal_imp) :: pat_binders) formals1
                         t_res args2
                     else
                       (let x1 =
                          let uu___1657_11639 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___1657_11639.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___1657_11639.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort =
                              (formal.FStar_Syntax_Syntax.sort)
                          }  in
                        let subst1 =
                          let uu____11643 =
                            let uu____11644 =
                              let uu____11651 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              (formal, uu____11651)  in
                            FStar_Syntax_Syntax.NT uu____11644  in
                          [uu____11643]  in
                        let formals2 =
                          FStar_Syntax_Subst.subst_binders subst1 formals1
                           in
                        let t_res1 = FStar_Syntax_Subst.subst subst1 t_res
                           in
                        aux
                          (((let uu___1663_11667 = x1  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___1663_11667.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___1663_11667.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort =
                                 (formal.FStar_Syntax_Syntax.sort)
                             }), a_imp) :: pat_binders) formals2 t_res1 args2)
                 | uu____11668 ->
                     aux ((formal, formal_imp) :: pat_binders) formals1 t_res
                       args2)
            | ([],args2) ->
                let uu____11708 =
                  let uu____11715 =
                    FStar_TypeChecker_Normalize.unfold_whnf env t_res  in
                  FStar_Syntax_Util.arrow_formals uu____11715  in
                (match uu____11708 with
                 | (more_formals,t_res1) ->
                     (match more_formals with
                      | [] -> FStar_Pervasives_Native.None
                      | uu____11774 ->
                          aux pat_binders more_formals t_res1 args2))
             in
          (match args with
           | [] -> FStar_Pervasives_Native.Some ([], t_hd)
           | uu____11799 ->
               let uu____11800 = FStar_Syntax_Util.arrow_formals t_hd  in
               (match uu____11800 with
                | (formals,t_res) -> aux [] formals t_res args))
  
let rec (solve : FStar_TypeChecker_Env.env -> worklist -> solution) =
  fun env  ->
    fun probs  ->
      (let uu____12132 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "Rel")
          in
       if uu____12132
       then
         let uu____12137 = wl_to_string probs  in
         FStar_Util.print1 "solve:\n\t%s\n" uu____12137
       else ());
      (let uu____12143 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ImplicitTrace")
          in
       if uu____12143
       then
         let uu____12148 =
           FStar_TypeChecker_Common.implicits_to_string probs.wl_implicits
            in
         FStar_Util.print1 "solve: wl_implicits = %s\n" uu____12148
       else ());
      (let uu____12153 = next_prob probs  in
       match uu____12153 with
       | FStar_Pervasives_Native.Some (hd1,tl1,rank1) ->
           let probs1 =
             let uu___1690_12180 = probs  in
             {
               attempting = tl1;
               wl_deferred = (uu___1690_12180.wl_deferred);
               wl_deferred_to_tac = (uu___1690_12180.wl_deferred_to_tac);
               ctr = (uu___1690_12180.ctr);
               defer_ok = (uu___1690_12180.defer_ok);
               smt_ok = (uu___1690_12180.smt_ok);
               umax_heuristic_ok = (uu___1690_12180.umax_heuristic_ok);
               tcenv = (uu___1690_12180.tcenv);
               wl_implicits = (uu___1690_12180.wl_implicits)
             }  in
           (def_check_prob "solve,hd" hd1;
            (match hd1 with
             | FStar_TypeChecker_Common.CProb cp ->
                 solve_c env (maybe_invert cp) probs1
             | FStar_TypeChecker_Common.TProb tp ->
                 let uu____12189 =
                   FStar_Util.physical_equality
                     tp.FStar_TypeChecker_Common.lhs
                     tp.FStar_TypeChecker_Common.rhs
                    in
                 if uu____12189
                 then
                   let uu____12192 =
                     solve_prob hd1 FStar_Pervasives_Native.None [] probs1
                      in
                   solve env uu____12192
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
                           (let uu___1702_12204 = tp  in
                            {
                              FStar_TypeChecker_Common.pid =
                                (uu___1702_12204.FStar_TypeChecker_Common.pid);
                              FStar_TypeChecker_Common.lhs =
                                (uu___1702_12204.FStar_TypeChecker_Common.lhs);
                              FStar_TypeChecker_Common.relation =
                                FStar_TypeChecker_Common.EQ;
                              FStar_TypeChecker_Common.rhs =
                                (uu___1702_12204.FStar_TypeChecker_Common.rhs);
                              FStar_TypeChecker_Common.element =
                                (uu___1702_12204.FStar_TypeChecker_Common.element);
                              FStar_TypeChecker_Common.logical_guard =
                                (uu___1702_12204.FStar_TypeChecker_Common.logical_guard);
                              FStar_TypeChecker_Common.logical_guard_uvar =
                                (uu___1702_12204.FStar_TypeChecker_Common.logical_guard_uvar);
                              FStar_TypeChecker_Common.reason =
                                (uu___1702_12204.FStar_TypeChecker_Common.reason);
                              FStar_TypeChecker_Common.loc =
                                (uu___1702_12204.FStar_TypeChecker_Common.loc);
                              FStar_TypeChecker_Common.rank =
                                (uu___1702_12204.FStar_TypeChecker_Common.rank)
                            }) probs1
                       else
                         solve_rigid_flex_or_flex_rigid_subtyping rank1 env
                           tp probs1))
       | FStar_Pervasives_Native.None  ->
           (match probs.wl_deferred with
            | [] ->
                let uu____12224 =
                  let uu____12231 = as_deferred probs.wl_deferred_to_tac  in
                  ([], uu____12231, (probs.wl_implicits))  in
                Success uu____12224
            | uu____12237 ->
                let uu____12247 =
                  FStar_All.pipe_right probs.wl_deferred
                    (FStar_List.partition
                       (fun uu____12312  ->
                          match uu____12312 with
                          | (c,uu____12322,uu____12323) -> c < probs.ctr))
                   in
                (match uu____12247 with
                 | (attempt1,rest) ->
                     (match attempt1 with
                      | [] ->
                          let uu____12371 =
                            let uu____12378 = as_deferred probs.wl_deferred
                               in
                            let uu____12379 =
                              as_deferred probs.wl_deferred_to_tac  in
                            (uu____12378, uu____12379, (probs.wl_implicits))
                             in
                          Success uu____12371
                      | uu____12380 ->
                          let uu____12390 =
                            let uu___1716_12391 = probs  in
                            let uu____12392 =
                              FStar_All.pipe_right attempt1
                                (FStar_List.map
                                   (fun uu____12413  ->
                                      match uu____12413 with
                                      | (uu____12421,uu____12422,y) -> y))
                               in
                            {
                              attempting = uu____12392;
                              wl_deferred = rest;
                              wl_deferred_to_tac =
                                (uu___1716_12391.wl_deferred_to_tac);
                              ctr = (uu___1716_12391.ctr);
                              defer_ok = (uu___1716_12391.defer_ok);
                              smt_ok = (uu___1716_12391.smt_ok);
                              umax_heuristic_ok =
                                (uu___1716_12391.umax_heuristic_ok);
                              tcenv = (uu___1716_12391.tcenv);
                              wl_implicits = (uu___1716_12391.wl_implicits)
                            }  in
                          solve env uu____12390))))

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
            let uu____12431 = solve_universe_eq (p_pid orig) wl u1 u2  in
            match uu____12431 with
            | USolved wl1 ->
                let uu____12433 =
                  solve_prob orig FStar_Pervasives_Native.None [] wl1  in
                solve env uu____12433
            | UFailed msg -> giveup env msg orig
            | UDeferred wl1 ->
                let uu____12436 = defer_lit "" orig wl1  in
                solve env uu____12436

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
                  let uu____12487 = solve_universe_eq (p_pid orig) wl1 u1 u2
                     in
                  (match uu____12487 with
                   | USolved wl2 -> aux wl2 us11 us21
                   | failed_or_deferred -> failed_or_deferred)
              | uu____12490 -> ufailed_simple "Unequal number of universes"
               in
            let t11 = whnf env t1  in
            let t21 = whnf env t2  in
            match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n))
            with
            | (FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                  FStar_Syntax_Syntax.pos = uu____12503;
                  FStar_Syntax_Syntax.vars = uu____12504;_},us1),FStar_Syntax_Syntax.Tm_uinst
               ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar g;
                  FStar_Syntax_Syntax.pos = uu____12507;
                  FStar_Syntax_Syntax.vars = uu____12508;_},us2))
                -> let b = FStar_Syntax_Syntax.fv_eq f g  in aux wl us1 us2
            | (FStar_Syntax_Syntax.Tm_uinst uu____12521,uu____12522) ->
                failwith "Impossible: expect head symbols to match"
            | (uu____12530,FStar_Syntax_Syntax.Tm_uinst uu____12531) ->
                failwith "Impossible: expect head symbols to match"
            | uu____12539 -> USolved wl

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
            ((let uu____12550 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____12550
              then
                let uu____12555 = prob_to_string env orig  in
                let uu____12557 = FStar_Thunk.force msg  in
                FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n"
                  uu____12555 uu____12557
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
            let uu___1798_12572 = wl1  in
            let uu____12573 =
              let uu____12583 =
                let uu____12591 = FStar_Thunk.mkv reason  in
                ((wl1.ctr), uu____12591, orig)  in
              uu____12583 :: (wl1.wl_deferred_to_tac)  in
            {
              attempting = (uu___1798_12572.attempting);
              wl_deferred = (uu___1798_12572.wl_deferred);
              wl_deferred_to_tac = uu____12573;
              ctr = (uu___1798_12572.ctr);
              defer_ok = (uu___1798_12572.defer_ok);
              smt_ok = (uu___1798_12572.smt_ok);
              umax_heuristic_ok = (uu___1798_12572.umax_heuristic_ok);
              tcenv = (uu___1798_12572.tcenv);
              wl_implicits = (uu___1798_12572.wl_implicits)
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
                let uu____12620 = FStar_Syntax_Util.head_and_args t  in
                match uu____12620 with
                | (head1,uu____12644) ->
                    let uu____12669 =
                      let uu____12670 = FStar_Syntax_Subst.compress head1  in
                      uu____12670.FStar_Syntax_Syntax.n  in
                    (match uu____12669 with
                     | FStar_Syntax_Syntax.Tm_uvar (uv,uu____12680) ->
                         let uu____12697 =
                           should_defer_uvar_to_user_tac wl.tcenv uv  in
                         (uu____12697,
                           (uv.FStar_Syntax_Syntax.ctx_uvar_reason))
                     | uu____12701 -> (false, ""))
                 in
              let uu____12706 =
                should_defer_tac prob.FStar_TypeChecker_Common.lhs  in
              (match uu____12706 with
               | (l1,r1) ->
                   let uu____12719 =
                     should_defer_tac prob.FStar_TypeChecker_Common.rhs  in
                   (match uu____12719 with
                    | (l2,r2) ->
                        if l1 || l2
                        then
                          defer_to_user_tac env
                            (FStar_TypeChecker_Common.TProb prob)
                            (Prims.op_Hat r1 (Prims.op_Hat ", " r2)) wl
                        else
                          (let uu____12736 =
                             defer_lit reason
                               (FStar_TypeChecker_Common.TProb prob) wl
                              in
                           solve env uu____12736)))
          | uu____12737 ->
              let uu____12738 =
                defer_lit reason (FStar_TypeChecker_Common.TProb prob) wl  in
              solve env uu____12738

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
               let uu____12824 =
                 new_problem wl2 env1 t1 FStar_TypeChecker_Common.EQ t2
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                   "join/meet refinements"
                  in
               match uu____12824 with
               | (p,wl3) ->
                   (def_check_prob "meet_or_join"
                      (FStar_TypeChecker_Common.TProb p);
                    ((FStar_TypeChecker_Common.TProb p), wl3))
                in
             let pairwise t1 t2 wl2 =
               (let uu____12879 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                    (FStar_Options.Other "Rel")
                   in
                if uu____12879
                then
                  let uu____12884 = FStar_Syntax_Print.term_to_string t1  in
                  let uu____12886 = FStar_Syntax_Print.term_to_string t2  in
                  FStar_Util.print2 "[meet/join]: pairwise: %s and %s\n"
                    uu____12884 uu____12886
                else ());
               (let uu____12891 = head_matches_delta env1 wl2 t1 t2  in
                match uu____12891 with
                | (mr,ts1) ->
                    (match mr with
                     | HeadMatch (true ) ->
                         let uu____12937 = eq_prob t1 t2 wl2  in
                         (match uu____12937 with | (p,wl3) -> (t1, [p], wl3))
                     | MisMatch uu____12958 ->
                         let uu____12967 = eq_prob t1 t2 wl2  in
                         (match uu____12967 with | (p,wl3) -> (t1, [p], wl3))
                     | FullMatch  ->
                         (match ts1 with
                          | FStar_Pervasives_Native.None  -> (t1, [], wl2)
                          | FStar_Pervasives_Native.Some (t11,t21) ->
                              (t11, [], wl2))
                     | HeadMatch (false ) ->
                         let uu____13017 =
                           match ts1 with
                           | FStar_Pervasives_Native.Some (t11,t21) ->
                               let uu____13032 =
                                 FStar_Syntax_Subst.compress t11  in
                               let uu____13033 =
                                 FStar_Syntax_Subst.compress t21  in
                               (uu____13032, uu____13033)
                           | FStar_Pervasives_Native.None  ->
                               let uu____13038 =
                                 FStar_Syntax_Subst.compress t1  in
                               let uu____13039 =
                                 FStar_Syntax_Subst.compress t2  in
                               (uu____13038, uu____13039)
                            in
                         (match uu____13017 with
                          | (t11,t21) ->
                              let try_eq t12 t22 wl3 =
                                let uu____13070 =
                                  FStar_Syntax_Util.head_and_args t12  in
                                match uu____13070 with
                                | (t1_hd,t1_args) ->
                                    let uu____13115 =
                                      FStar_Syntax_Util.head_and_args t22  in
                                    (match uu____13115 with
                                     | (t2_hd,t2_args) ->
                                         if
                                           (FStar_List.length t1_args) <>
                                             (FStar_List.length t2_args)
                                         then FStar_Pervasives_Native.None
                                         else
                                           (let uu____13181 =
                                              let uu____13188 =
                                                let uu____13199 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t1_hd
                                                   in
                                                uu____13199 :: t1_args  in
                                              let uu____13216 =
                                                let uu____13225 =
                                                  FStar_Syntax_Syntax.as_arg
                                                    t2_hd
                                                   in
                                                uu____13225 :: t2_args  in
                                              FStar_List.fold_left2
                                                (fun uu____13274  ->
                                                   fun uu____13275  ->
                                                     fun uu____13276  ->
                                                       match (uu____13274,
                                                               uu____13275,
                                                               uu____13276)
                                                       with
                                                       | ((probs,wl4),
                                                          (a1,uu____13326),
                                                          (a2,uu____13328))
                                                           ->
                                                           let uu____13365 =
                                                             eq_prob a1 a2
                                                               wl4
                                                              in
                                                           (match uu____13365
                                                            with
                                                            | (p,wl5) ->
                                                                ((p ::
                                                                  probs),
                                                                  wl5)))
                                                ([], wl3) uu____13188
                                                uu____13216
                                               in
                                            match uu____13181 with
                                            | (probs,wl4) ->
                                                let wl' =
                                                  let uu___1901_13391 = wl4
                                                     in
                                                  {
                                                    attempting = probs;
                                                    wl_deferred = [];
                                                    wl_deferred_to_tac =
                                                      (uu___1901_13391.wl_deferred_to_tac);
                                                    ctr =
                                                      (uu___1901_13391.ctr);
                                                    defer_ok = false;
                                                    smt_ok = false;
                                                    umax_heuristic_ok =
                                                      (uu___1901_13391.umax_heuristic_ok);
                                                    tcenv =
                                                      (uu___1901_13391.tcenv);
                                                    wl_implicits = []
                                                  }  in
                                                let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____13402 =
                                                  solve env1 wl'  in
                                                (match uu____13402 with
                                                 | Success
                                                     (uu____13405,defer_to_tac,imps)
                                                     ->
                                                     (FStar_Syntax_Unionfind.commit
                                                        tx;
                                                      (let uu____13409 =
                                                         extend_wl wl4
                                                           defer_to_tac imps
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____13409))
                                                 | Failed uu____13410 ->
                                                     (FStar_Syntax_Unionfind.rollback
                                                        tx;
                                                      FStar_Pervasives_Native.None))))
                                 in
                              let combine t12 t22 wl3 =
                                let uu____13442 =
                                  base_and_refinement_maybe_delta false env1
                                    t12
                                   in
                                match uu____13442 with
                                | (t1_base,p1_opt) ->
                                    let uu____13478 =
                                      base_and_refinement_maybe_delta false
                                        env1 t22
                                       in
                                    (match uu____13478 with
                                     | (t2_base,p2_opt) ->
                                         let combine_refinements t_base
                                           p1_opt1 p2_opt1 =
                                           let refine1 x t =
                                             let uu____13577 =
                                               FStar_Syntax_Util.is_t_true t
                                                in
                                             if uu____13577
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
                                               let uu____13630 =
                                                 op phi11 phi21  in
                                               refine1 x1 uu____13630
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
                                               let uu____13662 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13662
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
                                               let uu____13694 =
                                                 op FStar_Syntax_Util.t_true
                                                   phi1
                                                  in
                                               refine1 x1 uu____13694
                                           | uu____13697 -> t_base  in
                                         let uu____13714 =
                                           try_eq t1_base t2_base wl3  in
                                         (match uu____13714 with
                                          | FStar_Pervasives_Native.Some wl4
                                              ->
                                              let uu____13728 =
                                                combine_refinements t1_base
                                                  p1_opt p2_opt
                                                 in
                                              (uu____13728, [], wl4)
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____13735 =
                                                base_and_refinement_maybe_delta
                                                  true env1 t12
                                                 in
                                              (match uu____13735 with
                                               | (t1_base1,p1_opt1) ->
                                                   let uu____13771 =
                                                     base_and_refinement_maybe_delta
                                                       true env1 t22
                                                      in
                                                   (match uu____13771 with
                                                    | (t2_base1,p2_opt1) ->
                                                        let uu____13807 =
                                                          eq_prob t1_base1
                                                            t2_base1 wl3
                                                           in
                                                        (match uu____13807
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
                              let uu____13831 = combine t11 t21 wl2  in
                              (match uu____13831 with
                               | (t12,ps,wl3) ->
                                   ((let uu____13864 =
                                       FStar_All.pipe_left
                                         (FStar_TypeChecker_Env.debug env1)
                                         (FStar_Options.Other "Rel")
                                        in
                                     if uu____13864
                                     then
                                       let uu____13869 =
                                         FStar_Syntax_Print.term_to_string
                                           t12
                                          in
                                       FStar_Util.print1
                                         "pairwise fallback2 succeeded: %s"
                                         uu____13869
                                     else ());
                                    (t12, ps, wl3))))))
                in
             let rec aux uu____13911 ts1 =
               match uu____13911 with
               | (out,probs,wl2) ->
                   (match ts1 with
                    | [] -> (out, probs, wl2)
                    | t::ts2 ->
                        let uu____13974 = pairwise out t wl2  in
                        (match uu____13974 with
                         | (out1,probs',wl3) ->
                             aux
                               (out1, (FStar_List.append probs probs'), wl3)
                               ts2))
                in
             let uu____14010 =
               let uu____14021 = FStar_List.hd ts  in (uu____14021, [], wl1)
                in
             let uu____14030 = FStar_List.tl ts  in
             aux uu____14010 uu____14030  in
           let uu____14037 =
             if flip
             then
               ((tp.FStar_TypeChecker_Common.lhs),
                 (tp.FStar_TypeChecker_Common.rhs))
             else
               ((tp.FStar_TypeChecker_Common.rhs),
                 (tp.FStar_TypeChecker_Common.lhs))
              in
           match uu____14037 with
           | (this_flex,this_rigid) ->
               let uu____14063 =
                 let uu____14064 = FStar_Syntax_Subst.compress this_rigid  in
                 uu____14064.FStar_Syntax_Syntax.n  in
               (match uu____14063 with
                | FStar_Syntax_Syntax.Tm_arrow (_bs,comp) ->
                    let uu____14089 =
                      FStar_Syntax_Util.is_tot_or_gtot_comp comp  in
                    if uu____14089
                    then
                      let uu____14092 = destruct_flex_t this_flex wl  in
                      (match uu____14092 with
                       | (flex,wl1) ->
                           let uu____14099 = quasi_pattern env flex  in
                           (match uu____14099 with
                            | FStar_Pervasives_Native.None  ->
                                giveup_lit env
                                  "flex-arrow subtyping, not a quasi pattern"
                                  (FStar_TypeChecker_Common.TProb tp)
                            | FStar_Pervasives_Native.Some (flex_bs,flex_t)
                                ->
                                ((let uu____14118 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env)
                                      (FStar_Options.Other "Rel")
                                     in
                                  if uu____14118
                                  then
                                    let uu____14123 =
                                      FStar_Util.string_of_int
                                        tp.FStar_TypeChecker_Common.pid
                                       in
                                    FStar_Util.print1
                                      "Trying to solve by imitating arrow:%s\n"
                                      uu____14123
                                  else ());
                                 imitate_arrow
                                   (FStar_TypeChecker_Common.TProb tp) env
                                   wl1 flex flex_bs flex_t
                                   tp.FStar_TypeChecker_Common.relation
                                   this_rigid)))
                    else
                      (let uu____14130 =
                         attempt
                           [FStar_TypeChecker_Common.TProb
                              ((let uu___2011_14133 = tp  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2011_14133.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs =
                                    (uu___2011_14133.FStar_TypeChecker_Common.lhs);
                                  FStar_TypeChecker_Common.relation =
                                    FStar_TypeChecker_Common.EQ;
                                  FStar_TypeChecker_Common.rhs =
                                    (uu___2011_14133.FStar_TypeChecker_Common.rhs);
                                  FStar_TypeChecker_Common.element =
                                    (uu___2011_14133.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2011_14133.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2011_14133.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2011_14133.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2011_14133.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2011_14133.FStar_TypeChecker_Common.rank)
                                }))] wl
                          in
                       solve env uu____14130)
                | uu____14134 ->
                    ((let uu____14136 =
                        FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "Rel")
                         in
                      if uu____14136
                      then
                        let uu____14141 =
                          FStar_Util.string_of_int
                            tp.FStar_TypeChecker_Common.pid
                           in
                        FStar_Util.print1
                          "Trying to solve by meeting refinements:%s\n"
                          uu____14141
                      else ());
                     (let uu____14146 =
                        FStar_Syntax_Util.head_and_args this_flex  in
                      match uu____14146 with
                      | (u,_args) ->
                          let uu____14189 =
                            let uu____14190 = FStar_Syntax_Subst.compress u
                               in
                            uu____14190.FStar_Syntax_Syntax.n  in
                          (match uu____14189 with
                           | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar,_subst) ->
                               let equiv1 t =
                                 let uu____14218 =
                                   FStar_Syntax_Util.head_and_args t  in
                                 match uu____14218 with
                                 | (u',uu____14237) ->
                                     let uu____14262 =
                                       let uu____14263 = whnf env u'  in
                                       uu____14263.FStar_Syntax_Syntax.n  in
                                     (match uu____14262 with
                                      | FStar_Syntax_Syntax.Tm_uvar
                                          (ctx_uvar',_subst') ->
                                          FStar_Syntax_Unionfind.equiv
                                            ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_head
                                            ctx_uvar'.FStar_Syntax_Syntax.ctx_uvar_head
                                      | uu____14285 -> false)
                                  in
                               let uu____14287 =
                                 FStar_All.pipe_right wl.attempting
                                   (FStar_List.partition
                                      (fun uu___26_14310  ->
                                         match uu___26_14310 with
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
                                              | uu____14324 -> false)
                                         | uu____14328 -> false))
                                  in
                               (match uu____14287 with
                                | (bounds_probs,rest) ->
                                    let bounds_typs =
                                      let uu____14343 = whnf env this_rigid
                                         in
                                      let uu____14344 =
                                        FStar_List.collect
                                          (fun uu___27_14350  ->
                                             match uu___27_14350 with
                                             | FStar_TypeChecker_Common.TProb
                                                 p ->
                                                 let uu____14356 =
                                                   if flip
                                                   then
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.rhs
                                                   else
                                                     whnf env
                                                       (maybe_invert p).FStar_TypeChecker_Common.lhs
                                                    in
                                                 [uu____14356]
                                             | uu____14360 -> [])
                                          bounds_probs
                                         in
                                      uu____14343 :: uu____14344  in
                                    let uu____14361 =
                                      meet_or_join
                                        (if flip
                                         then FStar_Syntax_Util.mk_conj_simp
                                         else FStar_Syntax_Util.mk_disj_simp)
                                        bounds_typs env wl
                                       in
                                    (match uu____14361 with
                                     | (bound,sub_probs,wl1) ->
                                         let uu____14394 =
                                           let flex_u =
                                             flex_uvar_head this_flex  in
                                           let bound1 =
                                             let uu____14409 =
                                               let uu____14410 =
                                                 FStar_Syntax_Subst.compress
                                                   bound
                                                  in
                                               uu____14410.FStar_Syntax_Syntax.n
                                                in
                                             match uu____14409 with
                                             | FStar_Syntax_Syntax.Tm_refine
                                                 (x,phi) when
                                                 (tp.FStar_TypeChecker_Common.relation
                                                    =
                                                    FStar_TypeChecker_Common.SUB)
                                                   &&
                                                   (let uu____14422 =
                                                      occurs flex_u
                                                        x.FStar_Syntax_Syntax.sort
                                                       in
                                                    FStar_Pervasives_Native.snd
                                                      uu____14422)
                                                 ->
                                                 x.FStar_Syntax_Syntax.sort
                                             | uu____14433 -> bound  in
                                           let uu____14434 =
                                             new_problem wl1 env bound1
                                               FStar_TypeChecker_Common.EQ
                                               this_flex
                                               FStar_Pervasives_Native.None
                                               tp.FStar_TypeChecker_Common.loc
                                               (if flip
                                                then "joining refinements"
                                                else "meeting refinements")
                                              in
                                           (bound1, uu____14434)  in
                                         (match uu____14394 with
                                          | (bound_typ,(eq_prob,wl')) ->
                                              (def_check_prob "meet_or_join2"
                                                 (FStar_TypeChecker_Common.TProb
                                                    eq_prob);
                                               (let uu____14469 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "Rel")
                                                   in
                                                if uu____14469
                                                then
                                                  let wl'1 =
                                                    let uu___2071_14475 = wl1
                                                       in
                                                    {
                                                      attempting =
                                                        ((FStar_TypeChecker_Common.TProb
                                                            eq_prob) ::
                                                        sub_probs);
                                                      wl_deferred =
                                                        (uu___2071_14475.wl_deferred);
                                                      wl_deferred_to_tac =
                                                        (uu___2071_14475.wl_deferred_to_tac);
                                                      ctr =
                                                        (uu___2071_14475.ctr);
                                                      defer_ok =
                                                        (uu___2071_14475.defer_ok);
                                                      smt_ok =
                                                        (uu___2071_14475.smt_ok);
                                                      umax_heuristic_ok =
                                                        (uu___2071_14475.umax_heuristic_ok);
                                                      tcenv =
                                                        (uu___2071_14475.tcenv);
                                                      wl_implicits =
                                                        (uu___2071_14475.wl_implicits)
                                                    }  in
                                                  let uu____14476 =
                                                    wl_to_string wl'1  in
                                                  FStar_Util.print1
                                                    "After meet/join refinements: %s\n"
                                                    uu____14476
                                                else ());
                                               (let tx =
                                                  FStar_Syntax_Unionfind.new_transaction
                                                    ()
                                                   in
                                                let uu____14482 =
                                                  solve_t env eq_prob
                                                    (let uu___2076_14484 =
                                                       wl'  in
                                                     {
                                                       attempting = sub_probs;
                                                       wl_deferred =
                                                         (uu___2076_14484.wl_deferred);
                                                       wl_deferred_to_tac =
                                                         (uu___2076_14484.wl_deferred_to_tac);
                                                       ctr =
                                                         (uu___2076_14484.ctr);
                                                       defer_ok = false;
                                                       smt_ok =
                                                         (uu___2076_14484.smt_ok);
                                                       umax_heuristic_ok =
                                                         (uu___2076_14484.umax_heuristic_ok);
                                                       tcenv =
                                                         (uu___2076_14484.tcenv);
                                                       wl_implicits = []
                                                     })
                                                   in
                                                match uu____14482 with
                                                | Success
                                                    (uu____14486,defer_to_tac,imps)
                                                    ->
                                                    let wl2 =
                                                      let uu___2083_14490 =
                                                        wl'  in
                                                      {
                                                        attempting = rest;
                                                        wl_deferred =
                                                          (uu___2083_14490.wl_deferred);
                                                        wl_deferred_to_tac =
                                                          (uu___2083_14490.wl_deferred_to_tac);
                                                        ctr =
                                                          (uu___2083_14490.ctr);
                                                        defer_ok =
                                                          (uu___2083_14490.defer_ok);
                                                        smt_ok =
                                                          (uu___2083_14490.smt_ok);
                                                        umax_heuristic_ok =
                                                          (uu___2083_14490.umax_heuristic_ok);
                                                        tcenv =
                                                          (uu___2083_14490.tcenv);
                                                        wl_implicits =
                                                          (uu___2083_14490.wl_implicits)
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
                                                    let uu____14507 =
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
                                                    ((let uu____14519 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env)
                                                          (FStar_Options.Other
                                                             "Rel")
                                                         in
                                                      if uu____14519
                                                      then
                                                        let uu____14524 =
                                                          let uu____14526 =
                                                            FStar_List.map
                                                              (prob_to_string
                                                                 env)
                                                              ((FStar_TypeChecker_Common.TProb
                                                                  eq_prob) ::
                                                              sub_probs)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____14526
                                                            (FStar_String.concat
                                                               "\n")
                                                           in
                                                        FStar_Util.print1
                                                          "meet/join attempted and failed to solve problems:\n%s\n"
                                                          uu____14524
                                                      else ());
                                                     (let uu____14539 =
                                                        let uu____14554 =
                                                          base_and_refinement
                                                            env bound_typ
                                                           in
                                                        (rank1, uu____14554)
                                                         in
                                                      match uu____14539 with
                                                      | (FStar_TypeChecker_Common.Rigid_flex
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           uu____14576))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14602 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14602
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
                                                                  let uu____14622
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14622))))
                                                      | (FStar_TypeChecker_Common.Flex_rigid
                                                         ,(t_base,FStar_Pervasives_Native.Some
                                                           (x,phi)))
                                                          ->
                                                          (FStar_Syntax_Unionfind.rollback
                                                             tx;
                                                           (let uu____14647 =
                                                              new_problem wl1
                                                                env t_base
                                                                FStar_TypeChecker_Common.EQ
                                                                this_flex
                                                                FStar_Pervasives_Native.None
                                                                tp.FStar_TypeChecker_Common.loc
                                                                "widened subtyping"
                                                               in
                                                            match uu____14647
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
                                                                    let uu____14667
                                                                    =
                                                                    let uu____14672
                                                                    =
                                                                    FStar_Syntax_Util.mk_conj
                                                                    phi1
                                                                    (p_guard
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    eq_prob1))
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____14672
                                                                     in
                                                                    solve_prob'
                                                                    false
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    tp)
                                                                    uu____14667
                                                                    [] wl2
                                                                     in
                                                                  let uu____14678
                                                                    =
                                                                    attempt
                                                                    [
                                                                    FStar_TypeChecker_Common.TProb
                                                                    eq_prob1]
                                                                    wl3  in
                                                                  solve env
                                                                    uu____14678))))
                                                      | uu____14679 ->
                                                          let uu____14694 =
                                                            FStar_Thunk.map
                                                              (fun s  ->
                                                                 Prims.op_Hat
                                                                   "failed to solve the sub-problems: "
                                                                   s) msg
                                                             in
                                                          giveup env
                                                            uu____14694 p)))))))
                           | uu____14701 when flip ->
                               let uu____14702 =
                                 let uu____14704 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14706 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a flex-rigid: %s"
                                   uu____14704 uu____14706
                                  in
                               failwith uu____14702
                           | uu____14709 ->
                               let uu____14710 =
                                 let uu____14712 =
                                   FStar_Util.string_of_int
                                     (rank_t_num rank1)
                                    in
                                 let uu____14714 =
                                   prob_to_string env
                                     (FStar_TypeChecker_Common.TProb tp)
                                    in
                                 FStar_Util.format2
                                   "Impossible: (rank=%s) Not a rigid-flex: %s"
                                   uu____14712 uu____14714
                                  in
                               failwith uu____14710)))))

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
                      (fun uu____14750  ->
                         match uu____14750 with
                         | (x,i) ->
                             let uu____14769 =
                               FStar_Syntax_Syntax.bv_to_name x  in
                             (uu____14769, i)) bs_lhs
                     in
                  let uu____14772 = lhs  in
                  match uu____14772 with
                  | Flex (uu____14773,u_lhs,uu____14775) ->
                      let imitate_comp bs bs_terms c wl1 =
                        let imitate_tot_or_gtot t uopt f wl2 =
                          let uu____14872 =
                            match uopt with
                            | FStar_Pervasives_Native.None  ->
                                FStar_Syntax_Util.type_u ()
                            | FStar_Pervasives_Native.Some univ ->
                                let uu____14882 =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type univ)
                                    FStar_Pervasives_Native.None
                                    t.FStar_Syntax_Syntax.pos
                                   in
                                (uu____14882, univ)
                             in
                          match uu____14872 with
                          | (k,univ) ->
                              let uu____14889 =
                                copy_uvar u_lhs (FStar_List.append bs_lhs bs)
                                  k wl2
                                 in
                              (match uu____14889 with
                               | (uu____14906,u,wl3) ->
                                   let uu____14909 =
                                     f u (FStar_Pervasives_Native.Some univ)
                                      in
                                   (uu____14909, wl3))
                           in
                        match c.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Total (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_Total' wl1
                        | FStar_Syntax_Syntax.GTotal (t,uopt) ->
                            imitate_tot_or_gtot t uopt
                              FStar_Syntax_Syntax.mk_GTotal' wl1
                        | FStar_Syntax_Syntax.Comp ct ->
                            let uu____14935 =
                              let uu____14948 =
                                let uu____14959 =
                                  FStar_Syntax_Syntax.as_arg
                                    ct.FStar_Syntax_Syntax.result_typ
                                   in
                                uu____14959 ::
                                  (ct.FStar_Syntax_Syntax.effect_args)
                                 in
                              FStar_List.fold_right
                                (fun uu____15010  ->
                                   fun uu____15011  ->
                                     match (uu____15010, uu____15011) with
                                     | ((a,i),(out_args,wl2)) ->
                                         let uu____15112 =
                                           let uu____15119 =
                                             let uu____15122 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             FStar_All.pipe_left
                                               FStar_Pervasives_Native.fst
                                               uu____15122
                                              in
                                           copy_uvar u_lhs [] uu____15119 wl2
                                            in
                                         (match uu____15112 with
                                          | (uu____15151,t_a,wl3) ->
                                              let uu____15154 =
                                                copy_uvar u_lhs bs t_a wl3
                                                 in
                                              (match uu____15154 with
                                               | (uu____15173,a',wl4) ->
                                                   (((a', i) :: out_args),
                                                     wl4)))) uu____14948
                                ([], wl1)
                               in
                            (match uu____14935 with
                             | (out_args,wl2) ->
                                 let ct' =
                                   let uu___2196_15229 = ct  in
                                   let uu____15230 =
                                     let uu____15233 = FStar_List.hd out_args
                                        in
                                     FStar_Pervasives_Native.fst uu____15233
                                      in
                                   let uu____15248 = FStar_List.tl out_args
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___2196_15229.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_name =
                                       (uu___2196_15229.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       uu____15230;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____15248;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___2196_15229.FStar_Syntax_Syntax.flags)
                                   }  in
                                 ((let uu___2199_15266 = c  in
                                   {
                                     FStar_Syntax_Syntax.n =
                                       (FStar_Syntax_Syntax.Comp ct');
                                     FStar_Syntax_Syntax.pos =
                                       (uu___2199_15266.FStar_Syntax_Syntax.pos);
                                     FStar_Syntax_Syntax.vars =
                                       (uu___2199_15266.FStar_Syntax_Syntax.vars)
                                   }), wl2))
                         in
                      let uu____15269 =
                        FStar_Syntax_Util.arrow_formals_comp arrow1  in
                      (match uu____15269 with
                       | (formals,c) ->
                           let rec aux bs bs_terms formals1 wl1 =
                             match formals1 with
                             | [] ->
                                 let uu____15307 =
                                   imitate_comp bs bs_terms c wl1  in
                                 (match uu____15307 with
                                  | (c',wl2) ->
                                      let lhs' =
                                        FStar_Syntax_Util.arrow bs c'  in
                                      let sol =
                                        let uu____15318 =
                                          let uu____15323 =
                                            FStar_Syntax_Util.abs bs_lhs lhs'
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____15323)  in
                                        TERM uu____15318  in
                                      let uu____15324 =
                                        mk_t_problem wl2 [] orig lhs' rel
                                          arrow1 FStar_Pervasives_Native.None
                                          "arrow imitation"
                                         in
                                      (match uu____15324 with
                                       | (sub_prob,wl3) ->
                                           let uu____15338 =
                                             let uu____15339 =
                                               solve_prob orig
                                                 FStar_Pervasives_Native.None
                                                 [sol] wl3
                                                in
                                             attempt [sub_prob] uu____15339
                                              in
                                           solve env uu____15338))
                             | (x,imp)::formals2 ->
                                 let uu____15361 =
                                   let uu____15368 =
                                     let uu____15371 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_right uu____15371
                                       FStar_Pervasives_Native.fst
                                      in
                                   copy_uvar u_lhs
                                     (FStar_List.append bs_lhs bs)
                                     uu____15368 wl1
                                    in
                                 (match uu____15361 with
                                  | (_ctx_u_x,u_x,wl2) ->
                                      let y =
                                        let uu____15392 =
                                          let uu____15395 =
                                            FStar_Syntax_Syntax.range_of_bv x
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____15395
                                           in
                                        FStar_Syntax_Syntax.new_bv
                                          uu____15392 u_x
                                         in
                                      let uu____15396 =
                                        let uu____15399 =
                                          let uu____15402 =
                                            let uu____15403 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                y
                                               in
                                            (uu____15403, imp)  in
                                          [uu____15402]  in
                                        FStar_List.append bs_terms
                                          uu____15399
                                         in
                                      aux (FStar_List.append bs [(y, imp)])
                                        uu____15396 formals2 wl2)
                              in
                           let uu____15430 = occurs_check u_lhs arrow1  in
                           (match uu____15430 with
                            | (uu____15443,occurs_ok,msg) ->
                                if Prims.op_Negation occurs_ok
                                then
                                  let uu____15459 =
                                    FStar_Thunk.mk
                                      (fun uu____15463  ->
                                         let uu____15464 =
                                           FStar_Option.get msg  in
                                         Prims.op_Hat "occurs-check failed: "
                                           uu____15464)
                                     in
                                  giveup_or_defer env orig wl uu____15459
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
              (let uu____15497 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____15497
               then
                 let uu____15502 =
                   FStar_Syntax_Print.binders_to_string ", " bs1  in
                 let uu____15505 =
                   FStar_Syntax_Print.binders_to_string ", " bs2  in
                 FStar_Util.print3 "solve_binders\n\t%s\n%s\n\t%s\n"
                   uu____15502 (rel_to_string (p_rel orig)) uu____15505
               else ());
              (let rec aux wl1 scope env1 subst1 xs ys =
                 match (xs, ys) with
                 | ([],[]) ->
                     let uu____15636 = rhs wl1 scope env1 subst1  in
                     (match uu____15636 with
                      | (rhs_prob,wl2) ->
                          ((let uu____15659 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env1)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____15659
                            then
                              let uu____15664 = prob_to_string env1 rhs_prob
                                 in
                              FStar_Util.print1 "rhs_prob = %s\n" uu____15664
                            else ());
                           (let formula = p_guard rhs_prob  in
                            (env1, (FStar_Util.Inl ([rhs_prob], formula)),
                              wl2))))
                 | ((hd1,imp)::xs1,(hd2,imp')::ys1) when
                     let uu____15742 = FStar_Syntax_Util.eq_aqual imp imp'
                        in
                     uu____15742 = FStar_Syntax_Util.Equal ->
                     let hd11 =
                       let uu___2269_15744 = hd1  in
                       let uu____15745 =
                         FStar_Syntax_Subst.subst subst1
                           hd1.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2269_15744.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2269_15744.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15745
                       }  in
                     let hd21 =
                       let uu___2272_15749 = hd2  in
                       let uu____15750 =
                         FStar_Syntax_Subst.subst subst1
                           hd2.FStar_Syntax_Syntax.sort
                          in
                       {
                         FStar_Syntax_Syntax.ppname =
                           (uu___2272_15749.FStar_Syntax_Syntax.ppname);
                         FStar_Syntax_Syntax.index =
                           (uu___2272_15749.FStar_Syntax_Syntax.index);
                         FStar_Syntax_Syntax.sort = uu____15750
                       }  in
                     let uu____15753 =
                       let uu____15758 =
                         FStar_All.pipe_left invert_rel (p_rel orig)  in
                       mk_t_problem wl1 scope orig
                         hd11.FStar_Syntax_Syntax.sort uu____15758
                         hd21.FStar_Syntax_Syntax.sort
                         FStar_Pervasives_Native.None "Formal parameter"
                        in
                     (match uu____15753 with
                      | (prob,wl2) ->
                          let hd12 = FStar_Syntax_Syntax.freshen_bv hd11  in
                          let subst2 =
                            let uu____15781 =
                              FStar_Syntax_Subst.shift_subst Prims.int_one
                                subst1
                               in
                            (FStar_Syntax_Syntax.DB (Prims.int_zero, hd12))
                              :: uu____15781
                             in
                          let env2 = FStar_TypeChecker_Env.push_bv env1 hd12
                             in
                          let uu____15788 =
                            aux wl2 (FStar_List.append scope [(hd12, imp)])
                              env2 subst2 xs1 ys1
                             in
                          (match uu____15788 with
                           | (env3,FStar_Util.Inl (sub_probs,phi),wl3) ->
                               let phi1 =
                                 let uu____15860 =
                                   FStar_TypeChecker_Env.close_forall env3
                                     [(hd12, imp)] phi
                                    in
                                 FStar_Syntax_Util.mk_conj (p_guard prob)
                                   uu____15860
                                  in
                               ((let uu____15878 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env3)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____15878
                                 then
                                   let uu____15883 =
                                     FStar_Syntax_Print.term_to_string phi1
                                      in
                                   let uu____15885 =
                                     FStar_Syntax_Print.bv_to_string hd12  in
                                   FStar_Util.print2
                                     "Formula is %s\n\thd1=%s\n" uu____15883
                                     uu____15885
                                 else ());
                                (env3,
                                  (FStar_Util.Inl ((prob :: sub_probs), phi1)),
                                  wl3))
                           | fail1 -> fail1))
                 | uu____15920 ->
                     (env1,
                       (FStar_Util.Inr "arity or argument-qualifier mismatch"),
                       wl1)
                  in
               let uu____15956 = aux wl [] env [] bs1 bs2  in
               match uu____15956 with
               | (env1,FStar_Util.Inr msg,wl1) -> giveup_lit env1 msg orig
               | (env1,FStar_Util.Inl (sub_probs,phi),wl1) ->
                   let wl2 =
                     solve_prob orig (FStar_Pervasives_Native.Some phi) []
                       wl1
                      in
                   let uu____16015 = attempt sub_probs wl2  in
                   solve env1 uu____16015)

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
            let uu___2310_16035 = wl  in
            {
              attempting = [];
              wl_deferred = [];
              wl_deferred_to_tac = (uu___2310_16035.wl_deferred_to_tac);
              ctr = (uu___2310_16035.ctr);
              defer_ok = false;
              smt_ok = false;
              umax_heuristic_ok = false;
              tcenv = (uu___2310_16035.tcenv);
              wl_implicits = []
            }  in
          let tx = FStar_Syntax_Unionfind.new_transaction ()  in
          let uu____16047 = try_solve env wl'  in
          match uu____16047 with
          | Success (uu____16048,defer_to_tac,imps) ->
              (FStar_Syntax_Unionfind.commit tx;
               (let wl1 = extend_wl wl defer_to_tac imps  in solve env wl1))
          | Failed (p,s) ->
              (FStar_Syntax_Unionfind.rollback tx; else_solve env wl (p, s))

and (solve_t : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t" (FStar_TypeChecker_Common.TProb problem);
        (let uu____16061 = compress_tprob wl.tcenv problem  in
         solve_t' env uu____16061 wl)

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
            let uu____16067 = should_defer_flex_to_user_tac wl lhs  in
            if uu____16067
            then defer_to_user_tac env orig (flex_reason lhs) wl
            else
              (let binders_as_bv_set bs =
                 let uu____16080 =
                   FStar_List.map FStar_Pervasives_Native.fst bs  in
                 FStar_Util.as_set uu____16080 FStar_Syntax_Syntax.order_bv
                  in
               let mk_solution env1 lhs1 bs rhs1 =
                 let uu____16114 = lhs1  in
                 match uu____16114 with
                 | Flex (uu____16117,ctx_u,uu____16119) ->
                     let sol =
                       match bs with
                       | [] -> rhs1
                       | uu____16127 ->
                           let uu____16128 = sn_binders env1 bs  in
                           u_abs ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                             uu____16128 rhs1
                        in
                     [TERM (ctx_u, sol)]
                  in
               let try_quasi_pattern orig1 env1 wl1 lhs1 rhs1 =
                 let uu____16177 = quasi_pattern env1 lhs1  in
                 match uu____16177 with
                 | FStar_Pervasives_Native.None  ->
                     ((FStar_Util.Inl "Not a quasi-pattern"), wl1)
                 | FStar_Pervasives_Native.Some (bs,uu____16211) ->
                     let uu____16216 = lhs1  in
                     (match uu____16216 with
                      | Flex (t_lhs,ctx_u,args) ->
                          let uu____16231 = occurs_check ctx_u rhs1  in
                          (match uu____16231 with
                           | (uvars1,occurs_ok,msg) ->
                               if Prims.op_Negation occurs_ok
                               then
                                 let uu____16282 =
                                   let uu____16290 =
                                     let uu____16292 = FStar_Option.get msg
                                        in
                                     Prims.op_Hat
                                       "quasi-pattern, occurs-check failed: "
                                       uu____16292
                                      in
                                   FStar_Util.Inl uu____16290  in
                                 (uu____16282, wl1)
                               else
                                 (let fvs_lhs =
                                    binders_as_bv_set
                                      (FStar_List.append
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_binders
                                         bs)
                                     in
                                  let fvs_rhs = FStar_Syntax_Free.names rhs1
                                     in
                                  let uu____16320 =
                                    let uu____16322 =
                                      FStar_Util.set_is_subset_of fvs_rhs
                                        fvs_lhs
                                       in
                                    Prims.op_Negation uu____16322  in
                                  if uu____16320
                                  then
                                    ((FStar_Util.Inl
                                        "quasi-pattern, free names on the RHS are not included in the LHS"),
                                      wl1)
                                  else
                                    (let uu____16349 =
                                       let uu____16357 =
                                         mk_solution env1 lhs1 bs rhs1  in
                                       FStar_Util.Inr uu____16357  in
                                     let uu____16363 =
                                       restrict_all_uvars ctx_u uvars1 wl1
                                        in
                                     (uu____16349, uu____16363)))))
                  in
               let imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1 =
                 let uu____16407 = FStar_Syntax_Util.head_and_args rhs1  in
                 match uu____16407 with
                 | (rhs_hd,args) ->
                     let uu____16450 = FStar_Util.prefix args  in
                     (match uu____16450 with
                      | (args_rhs,last_arg_rhs) ->
                          let rhs' =
                            FStar_Syntax_Syntax.mk_Tm_app rhs_hd args_rhs
                              FStar_Pervasives_Native.None
                              rhs1.FStar_Syntax_Syntax.pos
                             in
                          let uu____16522 = lhs1  in
                          (match uu____16522 with
                           | Flex (t_lhs,u_lhs,_lhs_args) ->
                               let uu____16526 =
                                 let uu____16537 =
                                   let uu____16544 =
                                     let uu____16547 =
                                       FStar_Syntax_Util.type_u ()  in
                                     FStar_All.pipe_left
                                       FStar_Pervasives_Native.fst
                                       uu____16547
                                      in
                                   copy_uvar u_lhs [] uu____16544 wl1  in
                                 match uu____16537 with
                                 | (uu____16574,t_last_arg,wl2) ->
                                     let uu____16577 =
                                       let uu____16584 =
                                         let uu____16585 =
                                           let uu____16594 =
                                             FStar_Syntax_Syntax.null_binder
                                               t_last_arg
                                              in
                                           [uu____16594]  in
                                         FStar_List.append bs_lhs uu____16585
                                          in
                                       copy_uvar u_lhs uu____16584 t_res_lhs
                                         wl2
                                        in
                                     (match uu____16577 with
                                      | (uu____16629,lhs',wl3) ->
                                          let uu____16632 =
                                            copy_uvar u_lhs bs_lhs t_last_arg
                                              wl3
                                             in
                                          (match uu____16632 with
                                           | (uu____16649,lhs'_last_arg,wl4)
                                               -> (lhs', lhs'_last_arg, wl4)))
                                  in
                               (match uu____16526 with
                                | (lhs',lhs'_last_arg,wl2) ->
                                    let sol =
                                      let uu____16670 =
                                        let uu____16671 =
                                          let uu____16676 =
                                            let uu____16677 =
                                              let uu____16680 =
                                                let uu____16685 =
                                                  let uu____16686 =
                                                    FStar_Syntax_Syntax.as_arg
                                                      lhs'_last_arg
                                                     in
                                                  [uu____16686]  in
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  lhs' uu____16685
                                                 in
                                              uu____16680
                                                FStar_Pervasives_Native.None
                                                t_lhs.FStar_Syntax_Syntax.pos
                                               in
                                            FStar_Syntax_Util.abs bs_lhs
                                              uu____16677
                                              (FStar_Pervasives_Native.Some
                                                 (FStar_Syntax_Util.residual_tot
                                                    t_res_lhs))
                                             in
                                          (u_lhs, uu____16676)  in
                                        TERM uu____16671  in
                                      [uu____16670]  in
                                    let uu____16711 =
                                      let uu____16718 =
                                        mk_t_problem wl2 [] orig1 lhs'
                                          FStar_TypeChecker_Common.EQ rhs'
                                          FStar_Pervasives_Native.None
                                          "first-order lhs"
                                         in
                                      match uu____16718 with
                                      | (p1,wl3) ->
                                          let uu____16738 =
                                            mk_t_problem wl3 [] orig1
                                              lhs'_last_arg
                                              FStar_TypeChecker_Common.EQ
                                              (FStar_Pervasives_Native.fst
                                                 last_arg_rhs)
                                              FStar_Pervasives_Native.None
                                              "first-order rhs"
                                             in
                                          (match uu____16738 with
                                           | (p2,wl4) -> ([p1; p2], wl4))
                                       in
                                    (match uu____16711 with
                                     | (sub_probs,wl3) ->
                                         let uu____16770 =
                                           let uu____16771 =
                                             solve_prob orig1
                                               FStar_Pervasives_Native.None
                                               sol wl3
                                              in
                                           attempt sub_probs uu____16771  in
                                         solve env1 uu____16770))))
                  in
               let first_order orig1 env1 wl1 lhs1 rhs1 =
                 let is_app rhs2 =
                   let uu____16805 = FStar_Syntax_Util.head_and_args rhs2  in
                   match uu____16805 with
                   | (uu____16823,args) ->
                       (match args with | [] -> false | uu____16859 -> true)
                    in
                 let is_arrow rhs2 =
                   let uu____16878 =
                     let uu____16879 = FStar_Syntax_Subst.compress rhs2  in
                     uu____16879.FStar_Syntax_Syntax.n  in
                   match uu____16878 with
                   | FStar_Syntax_Syntax.Tm_arrow uu____16883 -> true
                   | uu____16899 -> false  in
                 let uu____16901 = quasi_pattern env1 lhs1  in
                 match uu____16901 with
                 | FStar_Pervasives_Native.None  ->
                     let msg =
                       FStar_Thunk.mk
                         (fun uu____16919  ->
                            let uu____16920 = prob_to_string env1 orig1  in
                            FStar_Util.format1
                              "first_order heuristic cannot solve %s; lhs not a quasi-pattern"
                              uu____16920)
                        in
                     giveup_or_defer env1 orig1 wl1 msg
                 | FStar_Pervasives_Native.Some (bs_lhs,t_res_lhs) ->
                     let uu____16929 = is_app rhs1  in
                     if uu____16929
                     then
                       imitate_app orig1 env1 wl1 lhs1 bs_lhs t_res_lhs rhs1
                     else
                       (let uu____16934 = is_arrow rhs1  in
                        if uu____16934
                        then
                          imitate_arrow orig1 env1 wl1 lhs1 bs_lhs t_res_lhs
                            FStar_TypeChecker_Common.EQ rhs1
                        else
                          (let msg =
                             FStar_Thunk.mk
                               (fun uu____16946  ->
                                  let uu____16947 = prob_to_string env1 orig1
                                     in
                                  FStar_Util.format1
                                    "first_order heuristic cannot solve %s; rhs not an app or arrow"
                                    uu____16947)
                              in
                           giveup_or_defer env1 orig1 wl1 msg))
                  in
               match p_rel orig with
               | FStar_TypeChecker_Common.SUB  ->
                   if wl.defer_ok
                   then
                     let uu____16951 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16951
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.SUBINV  ->
                   if wl.defer_ok
                   then
                     let uu____16957 = FStar_Thunk.mkv "flex-rigid subtyping"
                        in
                     giveup_or_defer env orig wl uu____16957
                   else
                     solve_t_flex_rigid_eq env (make_prob_eq orig) wl lhs rhs
               | FStar_TypeChecker_Common.EQ  ->
                   let uu____16962 = lhs  in
                   (match uu____16962 with
                    | Flex (_t1,ctx_uv,args_lhs) ->
                        let uu____16966 =
                          pat_vars env
                            ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                            args_lhs
                           in
                        (match uu____16966 with
                         | FStar_Pervasives_Native.Some lhs_binders ->
                             let rhs1 = sn env rhs  in
                             let names_to_string1 fvs =
                               let uu____16984 =
                                 let uu____16988 =
                                   FStar_Util.set_elements fvs  in
                                 FStar_List.map
                                   FStar_Syntax_Print.bv_to_string
                                   uu____16988
                                  in
                               FStar_All.pipe_right uu____16984
                                 (FStar_String.concat ", ")
                                in
                             let fvs1 =
                               binders_as_bv_set
                                 (FStar_List.append
                                    ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                    lhs_binders)
                                in
                             let fvs2 = FStar_Syntax_Free.names rhs1  in
                             let uu____17009 = occurs_check ctx_uv rhs1  in
                             (match uu____17009 with
                              | (uvars1,occurs_ok,msg) ->
                                  if Prims.op_Negation occurs_ok
                                  then
                                    let uu____17038 =
                                      let uu____17039 =
                                        let uu____17041 =
                                          FStar_Option.get msg  in
                                        Prims.op_Hat "occurs-check failed: "
                                          uu____17041
                                         in
                                      FStar_All.pipe_left FStar_Thunk.mkv
                                        uu____17039
                                       in
                                    giveup_or_defer env orig wl uu____17038
                                  else
                                    (let uu____17049 =
                                       FStar_Util.set_is_subset_of fvs2 fvs1
                                        in
                                     if uu____17049
                                     then
                                       let sol =
                                         mk_solution env lhs lhs_binders rhs1
                                          in
                                       let wl1 =
                                         restrict_all_uvars ctx_uv uvars1 wl
                                          in
                                       let uu____17056 =
                                         solve_prob orig
                                           FStar_Pervasives_Native.None sol
                                           wl1
                                          in
                                       solve env uu____17056
                                     else
                                       if wl.defer_ok
                                       then
                                         (let msg1 =
                                            FStar_Thunk.mk
                                              (fun uu____17069  ->
                                                 let uu____17070 =
                                                   names_to_string1 fvs2  in
                                                 let uu____17072 =
                                                   names_to_string1 fvs1  in
                                                 let uu____17074 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", "
                                                     (FStar_List.append
                                                        ctx_uv.FStar_Syntax_Syntax.ctx_uvar_binders
                                                        lhs_binders)
                                                    in
                                                 FStar_Util.format3
                                                   "free names in the RHS {%s} are out of scope for the LHS: {%s}, {%s}"
                                                   uu____17070 uu____17072
                                                   uu____17074)
                                             in
                                          giveup_or_defer env orig wl msg1)
                                       else first_order orig env wl lhs rhs1))
                         | uu____17086 ->
                             if wl.defer_ok
                             then
                               let uu____17090 =
                                 FStar_Thunk.mkv "Not a pattern"  in
                               giveup_or_defer env orig wl uu____17090
                             else
                               (let uu____17095 =
                                  try_quasi_pattern orig env wl lhs rhs  in
                                match uu____17095 with
                                | (FStar_Util.Inr sol,wl1) ->
                                    let uu____17121 =
                                      solve_prob orig
                                        FStar_Pervasives_Native.None sol wl1
                                       in
                                    solve env uu____17121
                                | (FStar_Util.Inl msg,uu____17123) ->
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
                  let uu____17141 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17141
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.SUBINV  ->
                if wl.defer_ok
                then
                  let uu____17147 = FStar_Thunk.mkv "flex-flex subtyping"  in
                  giveup_or_defer env orig wl uu____17147
                else solve_t_flex_flex env (make_prob_eq orig) wl lhs rhs
            | FStar_TypeChecker_Common.EQ  ->
                let uu____17152 =
                  (should_defer_flex_to_user_tac wl lhs) ||
                    (should_defer_flex_to_user_tac wl rhs)
                   in
                if uu____17152
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
                    (let uu____17159 =
                       FStar_Thunk.mkv "flex-flex non-pattern"  in
                     giveup_or_defer env orig wl uu____17159)
                  else
                    (let uu____17164 =
                       let uu____17181 = quasi_pattern env lhs  in
                       let uu____17188 = quasi_pattern env rhs  in
                       (uu____17181, uu____17188)  in
                     match uu____17164 with
                     | (FStar_Pervasives_Native.Some
                        (binders_lhs,t_res_lhs),FStar_Pervasives_Native.Some
                        (binders_rhs,t_res_rhs)) ->
                         let uu____17231 = lhs  in
                         (match uu____17231 with
                          | Flex
                              ({ FStar_Syntax_Syntax.n = uu____17232;
                                 FStar_Syntax_Syntax.pos = range;
                                 FStar_Syntax_Syntax.vars = uu____17234;_},u_lhs,uu____17236)
                              ->
                              let uu____17239 = rhs  in
                              (match uu____17239 with
                               | Flex (uu____17240,u_rhs,uu____17242) ->
                                   let uu____17243 =
                                     (FStar_Syntax_Unionfind.equiv
                                        u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                        u_rhs.FStar_Syntax_Syntax.ctx_uvar_head)
                                       &&
                                       (binders_eq binders_lhs binders_rhs)
                                      in
                                   if uu____17243
                                   then
                                     let uu____17250 =
                                       solve_prob orig
                                         FStar_Pervasives_Native.None [] wl
                                        in
                                     solve env uu____17250
                                   else
                                     (let uu____17253 =
                                        maximal_prefix
                                          u_lhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                          u_rhs.FStar_Syntax_Syntax.ctx_uvar_binders
                                         in
                                      match uu____17253 with
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
                                          let uu____17285 =
                                            let uu____17292 =
                                              let uu____17295 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  t_res_lhs
                                                 in
                                              FStar_Syntax_Util.arrow zs
                                                uu____17295
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
                                              uu____17292
                                              FStar_Syntax_Syntax.Strict
                                              FStar_Pervasives_Native.None
                                             in
                                          (match uu____17285 with
                                           | (uu____17301,w,wl1) ->
                                               let w_app =
                                                 let uu____17307 =
                                                   let uu____17312 =
                                                     FStar_List.map
                                                       (fun uu____17323  ->
                                                          match uu____17323
                                                          with
                                                          | (z,uu____17331)
                                                              ->
                                                              let uu____17336
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  z
                                                                 in
                                                              FStar_Syntax_Syntax.as_arg
                                                                uu____17336)
                                                       zs
                                                      in
                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                     w uu____17312
                                                    in
                                                 uu____17307
                                                   FStar_Pervasives_Native.None
                                                   w.FStar_Syntax_Syntax.pos
                                                  in
                                               ((let uu____17338 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____17338
                                                 then
                                                   let uu____17343 =
                                                     let uu____17347 =
                                                       flex_t_to_string lhs
                                                        in
                                                     let uu____17349 =
                                                       let uu____17353 =
                                                         flex_t_to_string rhs
                                                          in
                                                       let uu____17355 =
                                                         let uu____17359 =
                                                           term_to_string w
                                                            in
                                                         let uu____17361 =
                                                           let uu____17365 =
                                                             FStar_Syntax_Print.binders_to_string
                                                               ", "
                                                               (FStar_List.append
                                                                  ctx_l
                                                                  binders_lhs)
                                                              in
                                                           let uu____17374 =
                                                             let uu____17378
                                                               =
                                                               FStar_Syntax_Print.binders_to_string
                                                                 ", "
                                                                 (FStar_List.append
                                                                    ctx_r
                                                                    binders_rhs)
                                                                in
                                                             let uu____17387
                                                               =
                                                               let uu____17391
                                                                 =
                                                                 FStar_Syntax_Print.binders_to_string
                                                                   ", " zs
                                                                  in
                                                               [uu____17391]
                                                                in
                                                             uu____17378 ::
                                                               uu____17387
                                                              in
                                                           uu____17365 ::
                                                             uu____17374
                                                            in
                                                         uu____17359 ::
                                                           uu____17361
                                                          in
                                                       uu____17353 ::
                                                         uu____17355
                                                        in
                                                     uu____17347 ::
                                                       uu____17349
                                                      in
                                                   FStar_Util.print
                                                     "flex-flex quasi:\n\tlhs=%s\n\trhs=%s\n\tsol=%s\n\tctx_l@binders_lhs=%s\n\tctx_r@binders_rhs=%s\n\tzs=%s\n"
                                                     uu____17343
                                                 else ());
                                                (let sol =
                                                   let s1 =
                                                     let uu____17408 =
                                                       let uu____17413 =
                                                         FStar_Syntax_Util.abs
                                                           binders_lhs w_app
                                                           (FStar_Pervasives_Native.Some
                                                              (FStar_Syntax_Util.residual_tot
                                                                 t_res_lhs))
                                                          in
                                                       (u_lhs, uu____17413)
                                                        in
                                                     TERM uu____17408  in
                                                   let uu____17414 =
                                                     FStar_Syntax_Unionfind.equiv
                                                       u_lhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                       u_rhs.FStar_Syntax_Syntax.ctx_uvar_head
                                                      in
                                                   if uu____17414
                                                   then [s1]
                                                   else
                                                     (let s2 =
                                                        let uu____17422 =
                                                          let uu____17427 =
                                                            FStar_Syntax_Util.abs
                                                              binders_rhs
                                                              w_app
                                                              (FStar_Pervasives_Native.Some
                                                                 (FStar_Syntax_Util.residual_tot
                                                                    t_res_lhs))
                                                             in
                                                          (u_rhs,
                                                            uu____17427)
                                                           in
                                                        TERM uu____17422  in
                                                      [s1; s2])
                                                    in
                                                 let uu____17428 =
                                                   solve_prob orig
                                                     FStar_Pervasives_Native.None
                                                     sol wl1
                                                    in
                                                 solve env uu____17428))))))
                     | uu____17429 ->
                         let uu____17446 =
                           FStar_Thunk.mkv "flex-flex: non-patterns"  in
                         giveup_or_defer env orig wl uu____17446)

and (solve_t' : FStar_TypeChecker_Env.env -> tprob -> worklist -> solution) =
  fun env  ->
    fun problem  ->
      fun wl  ->
        def_check_prob "solve_t'.1" (FStar_TypeChecker_Common.TProb problem);
        (let giveup_or_defer1 orig msg = giveup_or_defer env orig wl msg  in
         let rigid_heads_match env1 need_unif torig wl1 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____17500 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "Rel")
               in
            if uu____17500
            then
              let uu____17505 = FStar_Syntax_Print.term_to_string t1  in
              let uu____17507 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____17509 = FStar_Syntax_Print.term_to_string t2  in
              let uu____17511 = FStar_Syntax_Print.tag_of_term t2  in
              FStar_Util.print5 "Heads %s: %s (%s) and %s (%s)\n"
                (if need_unif then "need unification" else "match")
                uu____17505 uu____17507 uu____17509 uu____17511
            else ());
           (let uu____17522 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17522 with
            | (head1,args1) ->
                let uu____17565 = FStar_Syntax_Util.head_and_args t2  in
                (match uu____17565 with
                 | (head2,args2) ->
                     let solve_head_then wl2 k =
                       if need_unif
                       then k true wl2
                       else
                         (let uu____17635 =
                            solve_maybe_uinsts env1 orig head1 head2 wl2  in
                          match uu____17635 with
                          | USolved wl3 -> k true wl3
                          | UFailed msg -> giveup env1 msg orig
                          | UDeferred wl3 ->
                              let uu____17640 =
                                defer_lit "universe constraints" orig wl3  in
                              k false uu____17640)
                        in
                     let nargs = FStar_List.length args1  in
                     if nargs <> (FStar_List.length args2)
                     then
                       let uu____17661 =
                         FStar_Thunk.mk
                           (fun uu____17668  ->
                              let uu____17669 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17671 = args_to_string args1  in
                              let uu____17675 =
                                FStar_Syntax_Print.term_to_string head2  in
                              let uu____17677 = args_to_string args2  in
                              FStar_Util.format4
                                "unequal number of arguments: %s[%s] and %s[%s]"
                                uu____17669 uu____17671 uu____17675
                                uu____17677)
                          in
                       giveup env1 uu____17661 orig
                     else
                       (let uu____17684 =
                          (nargs = Prims.int_zero) ||
                            (let uu____17689 =
                               FStar_Syntax_Util.eq_args args1 args2  in
                             uu____17689 = FStar_Syntax_Util.Equal)
                           in
                        if uu____17684
                        then
                          (if need_unif
                           then
                             solve_t env1
                               (let uu___2582_17693 = problem  in
                                {
                                  FStar_TypeChecker_Common.pid =
                                    (uu___2582_17693.FStar_TypeChecker_Common.pid);
                                  FStar_TypeChecker_Common.lhs = head1;
                                  FStar_TypeChecker_Common.relation =
                                    (uu___2582_17693.FStar_TypeChecker_Common.relation);
                                  FStar_TypeChecker_Common.rhs = head2;
                                  FStar_TypeChecker_Common.element =
                                    (uu___2582_17693.FStar_TypeChecker_Common.element);
                                  FStar_TypeChecker_Common.logical_guard =
                                    (uu___2582_17693.FStar_TypeChecker_Common.logical_guard);
                                  FStar_TypeChecker_Common.logical_guard_uvar
                                    =
                                    (uu___2582_17693.FStar_TypeChecker_Common.logical_guard_uvar);
                                  FStar_TypeChecker_Common.reason =
                                    (uu___2582_17693.FStar_TypeChecker_Common.reason);
                                  FStar_TypeChecker_Common.loc =
                                    (uu___2582_17693.FStar_TypeChecker_Common.loc);
                                  FStar_TypeChecker_Common.rank =
                                    (uu___2582_17693.FStar_TypeChecker_Common.rank)
                                }) wl1
                           else
                             solve_head_then wl1
                               (fun ok  ->
                                  fun wl2  ->
                                    if ok
                                    then
                                      let uu____17703 =
                                        solve_prob orig
                                          FStar_Pervasives_Native.None [] wl2
                                         in
                                      solve env1 uu____17703
                                    else solve env1 wl2))
                        else
                          (let uu____17708 = base_and_refinement env1 t1  in
                           match uu____17708 with
                           | (base1,refinement1) ->
                               let uu____17733 = base_and_refinement env1 t2
                                  in
                               (match uu____17733 with
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
                                           let uu____17898 =
                                             FStar_List.fold_right
                                               (fun uu____17938  ->
                                                  fun uu____17939  ->
                                                    match (uu____17938,
                                                            uu____17939)
                                                    with
                                                    | (((a1,uu____17991),
                                                        (a2,uu____17993)),
                                                       (probs,wl3)) ->
                                                        let uu____18042 =
                                                          mk_problem wl3 []
                                                            orig a1
                                                            FStar_TypeChecker_Common.EQ
                                                            a2
                                                            FStar_Pervasives_Native.None
                                                            "index"
                                                           in
                                                        (match uu____18042
                                                         with
                                                         | (prob',wl4) ->
                                                             (((FStar_TypeChecker_Common.TProb
                                                                  prob') ::
                                                               probs), wl4)))
                                               argp ([], wl2)
                                              in
                                           match uu____17898 with
                                           | (subprobs,wl3) ->
                                               ((let uu____18085 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18085
                                                 then
                                                   let uu____18090 =
                                                     FStar_Syntax_Print.list_to_string
                                                       (prob_to_string env1)
                                                       subprobs
                                                      in
                                                   FStar_Util.print1
                                                     "Adding subproblems for arguments: %s"
                                                     uu____18090
                                                 else ());
                                                (let uu____18096 =
                                                   FStar_Options.defensive ()
                                                    in
                                                 if uu____18096
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
                                                    (let uu____18123 =
                                                       mk_sub_probs wl3  in
                                                     match uu____18123 with
                                                     | (subprobs,wl4) ->
                                                         let formula =
                                                           let uu____18139 =
                                                             FStar_List.map
                                                               (fun p  ->
                                                                  p_guard p)
                                                               subprobs
                                                              in
                                                           FStar_Syntax_Util.mk_conj_l
                                                             uu____18139
                                                            in
                                                         let wl5 =
                                                           solve_prob orig
                                                             (FStar_Pervasives_Native.Some
                                                                formula) []
                                                             wl4
                                                            in
                                                         let uu____18147 =
                                                           attempt subprobs
                                                             wl5
                                                            in
                                                         solve env2
                                                           uu____18147))
                                            in
                                         let solve_sub_probs_no_smt env2 wl2
                                           =
                                           solve_head_then wl2
                                             (fun ok  ->
                                                fun wl3  ->
                                                  let uu____18172 =
                                                    mk_sub_probs wl3  in
                                                  match uu____18172 with
                                                  | (subprobs,wl4) ->
                                                      let formula =
                                                        let uu____18188 =
                                                          FStar_List.map
                                                            (fun p  ->
                                                               p_guard p)
                                                            subprobs
                                                           in
                                                        FStar_Syntax_Util.mk_conj_l
                                                          uu____18188
                                                         in
                                                      let wl5 =
                                                        solve_prob orig
                                                          (FStar_Pervasives_Native.Some
                                                             formula) [] wl4
                                                         in
                                                      let uu____18196 =
                                                        attempt subprobs wl5
                                                         in
                                                      solve env2 uu____18196)
                                            in
                                         let unfold_and_retry d env2 wl2
                                           uu____18224 =
                                           match uu____18224 with
                                           | (prob,reason) ->
                                               ((let uu____18241 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env2)
                                                     (FStar_Options.Other
                                                        "Rel")
                                                    in
                                                 if uu____18241
                                                 then
                                                   let uu____18246 =
                                                     prob_to_string env2 orig
                                                      in
                                                   let uu____18248 =
                                                     prob_to_string env2 prob
                                                      in
                                                   let uu____18250 =
                                                     FStar_Thunk.force reason
                                                      in
                                                   FStar_Util.print3
                                                     "Failed to solve %s because sub-problem %s is not solvable without SMT because %s"
                                                     uu____18246 uu____18248
                                                     uu____18250
                                                 else ());
                                                (let uu____18256 =
                                                   let uu____18265 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t1
                                                      in
                                                   let uu____18268 =
                                                     FStar_TypeChecker_Normalize.unfold_head_once
                                                       env2 t2
                                                      in
                                                   (uu____18265, uu____18268)
                                                    in
                                                 match uu____18256 with
                                                 | (FStar_Pervasives_Native.Some
                                                    t1',FStar_Pervasives_Native.Some
                                                    t2') ->
                                                     let uu____18281 =
                                                       FStar_Syntax_Util.head_and_args
                                                         t1'
                                                        in
                                                     (match uu____18281 with
                                                      | (head1',uu____18299)
                                                          ->
                                                          let uu____18324 =
                                                            FStar_Syntax_Util.head_and_args
                                                              t2'
                                                             in
                                                          (match uu____18324
                                                           with
                                                           | (head2',uu____18342)
                                                               ->
                                                               let uu____18367
                                                                 =
                                                                 let uu____18372
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head1'
                                                                    head1
                                                                    in
                                                                 let uu____18373
                                                                   =
                                                                   FStar_Syntax_Util.eq_tm
                                                                    head2'
                                                                    head2
                                                                    in
                                                                 (uu____18372,
                                                                   uu____18373)
                                                                  in
                                                               (match uu____18367
                                                                with
                                                                | (FStar_Syntax_Util.Equal
                                                                   ,FStar_Syntax_Util.Equal
                                                                   ) ->
                                                                    (
                                                                    (
                                                                    let uu____18375
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18375
                                                                    then
                                                                    let uu____18380
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1  in
                                                                    let uu____18382
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t1'  in
                                                                    let uu____18384
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2  in
                                                                    let uu____18386
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t2'  in
                                                                    FStar_Util.print4
                                                                    "Unfolding didn't make progress ... got %s ~> %s;\nand %s ~> %s\n"
                                                                    uu____18380
                                                                    uu____18382
                                                                    uu____18384
                                                                    uu____18386
                                                                    else ());
                                                                    solve_sub_probs
                                                                    env2 wl2)
                                                                | uu____18391
                                                                    ->
                                                                    let torig'
                                                                    =
                                                                    let uu___2670_18399
                                                                    = torig
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Common.pid
                                                                    =
                                                                    (uu___2670_18399.FStar_TypeChecker_Common.pid);
                                                                    FStar_TypeChecker_Common.lhs
                                                                    = t1';
                                                                    FStar_TypeChecker_Common.relation
                                                                    =
                                                                    (uu___2670_18399.FStar_TypeChecker_Common.relation);
                                                                    FStar_TypeChecker_Common.rhs
                                                                    = t2';
                                                                    FStar_TypeChecker_Common.element
                                                                    =
                                                                    (uu___2670_18399.FStar_TypeChecker_Common.element);
                                                                    FStar_TypeChecker_Common.logical_guard
                                                                    =
                                                                    (uu___2670_18399.FStar_TypeChecker_Common.logical_guard);
                                                                    FStar_TypeChecker_Common.logical_guard_uvar
                                                                    =
                                                                    (uu___2670_18399.FStar_TypeChecker_Common.logical_guard_uvar);
                                                                    FStar_TypeChecker_Common.reason
                                                                    =
                                                                    (uu___2670_18399.FStar_TypeChecker_Common.reason);
                                                                    FStar_TypeChecker_Common.loc
                                                                    =
                                                                    (uu___2670_18399.FStar_TypeChecker_Common.loc);
                                                                    FStar_TypeChecker_Common.rank
                                                                    =
                                                                    (uu___2670_18399.FStar_TypeChecker_Common.rank)
                                                                    }  in
                                                                    ((
                                                                    let uu____18401
                                                                    =
                                                                    FStar_All.pipe_left
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env2)
                                                                    (FStar_Options.Other
                                                                    "Rel")
                                                                     in
                                                                    if
                                                                    uu____18401
                                                                    then
                                                                    let uu____18406
                                                                    =
                                                                    prob_to_string
                                                                    env2
                                                                    (FStar_TypeChecker_Common.TProb
                                                                    torig')
                                                                     in
                                                                    FStar_Util.print1
                                                                    "Unfolded and now trying %s\n"
                                                                    uu____18406
                                                                    else ());
                                                                    solve_t
                                                                    env2
                                                                    torig'
                                                                    wl2))))
                                                 | uu____18411 ->
                                                     solve_sub_probs env2 wl2))
                                            in
                                         let d =
                                           let uu____18423 =
                                             delta_depth_of_term env1 head1
                                              in
                                           match uu____18423 with
                                           | FStar_Pervasives_Native.None  ->
                                               FStar_Pervasives_Native.None
                                           | FStar_Pervasives_Native.Some d
                                               ->
                                               FStar_TypeChecker_Common.decr_delta_depth
                                                 d
                                            in
                                         let treat_as_injective =
                                           let uu____18431 =
                                             let uu____18432 =
                                               FStar_Syntax_Util.un_uinst
                                                 head1
                                                in
                                             uu____18432.FStar_Syntax_Syntax.n
                                              in
                                           match uu____18431 with
                                           | FStar_Syntax_Syntax.Tm_fvar fv
                                               ->
                                               FStar_TypeChecker_Env.fv_has_attr
                                                 env1 fv
                                                 FStar_Parser_Const.unifier_hint_injective_lid
                                           | uu____18437 -> false  in
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
                                          | uu____18440 ->
                                              solve_sub_probs env1 wl1)
                                     | uu____18443 ->
                                         let lhs =
                                           force_refinement
                                             (base1, refinement1)
                                            in
                                         let rhs =
                                           force_refinement
                                             (base2, refinement2)
                                            in
                                         solve_t env1
                                           (let uu___2690_18479 = problem  in
                                            {
                                              FStar_TypeChecker_Common.pid =
                                                (uu___2690_18479.FStar_TypeChecker_Common.pid);
                                              FStar_TypeChecker_Common.lhs =
                                                lhs;
                                              FStar_TypeChecker_Common.relation
                                                =
                                                (uu___2690_18479.FStar_TypeChecker_Common.relation);
                                              FStar_TypeChecker_Common.rhs =
                                                rhs;
                                              FStar_TypeChecker_Common.element
                                                =
                                                (uu___2690_18479.FStar_TypeChecker_Common.element);
                                              FStar_TypeChecker_Common.logical_guard
                                                =
                                                (uu___2690_18479.FStar_TypeChecker_Common.logical_guard);
                                              FStar_TypeChecker_Common.logical_guard_uvar
                                                =
                                                (uu___2690_18479.FStar_TypeChecker_Common.logical_guard_uvar);
                                              FStar_TypeChecker_Common.reason
                                                =
                                                (uu___2690_18479.FStar_TypeChecker_Common.reason);
                                              FStar_TypeChecker_Common.loc =
                                                (uu___2690_18479.FStar_TypeChecker_Common.loc);
                                              FStar_TypeChecker_Common.rank =
                                                (uu___2690_18479.FStar_TypeChecker_Common.rank)
                                            }) wl1))))))
            in
         let try_match_heuristic env1 orig wl1 s1 s2 t1t2_opt =
           let try_solve_branch scrutinee p =
             let uu____18555 = destruct_flex_t scrutinee wl1  in
             match uu____18555 with
             | (Flex (_t,uv,_args),wl2) ->
                 let uu____18566 =
                   FStar_TypeChecker_PatternUtils.pat_as_exp true env1 p  in
                 (match uu____18566 with
                  | (xs,pat_term,uu____18582,uu____18583) ->
                      let uu____18588 =
                        FStar_List.fold_left
                          (fun uu____18611  ->
                             fun x  ->
                               match uu____18611 with
                               | (subst1,wl3) ->
                                   let t_x =
                                     FStar_Syntax_Subst.subst subst1
                                       x.FStar_Syntax_Syntax.sort
                                      in
                                   let uu____18632 = copy_uvar uv [] t_x wl3
                                      in
                                   (match uu____18632 with
                                    | (uu____18651,u,wl4) ->
                                        let subst2 =
                                          (FStar_Syntax_Syntax.NT (x, u)) ::
                                          subst1  in
                                        (subst2, wl4))) ([], wl2) xs
                         in
                      (match uu____18588 with
                       | (subst1,wl3) ->
                           let pat_term1 =
                             FStar_Syntax_Subst.subst subst1 pat_term  in
                           let uu____18672 =
                             new_problem wl3 env1 scrutinee
                               FStar_TypeChecker_Common.EQ pat_term1
                               FStar_Pervasives_Native.None
                               scrutinee.FStar_Syntax_Syntax.pos
                               "match heuristic"
                              in
                           (match uu____18672 with
                            | (prob,wl4) ->
                                let wl' =
                                  let uu___2731_18689 = wl4  in
                                  {
                                    attempting =
                                      [FStar_TypeChecker_Common.TProb prob];
                                    wl_deferred = [];
                                    wl_deferred_to_tac =
                                      (uu___2731_18689.wl_deferred_to_tac);
                                    ctr = (uu___2731_18689.ctr);
                                    defer_ok = false;
                                    smt_ok = false;
                                    umax_heuristic_ok =
                                      (uu___2731_18689.umax_heuristic_ok);
                                    tcenv = (uu___2731_18689.tcenv);
                                    wl_implicits = []
                                  }  in
                                let tx =
                                  FStar_Syntax_Unionfind.new_transaction ()
                                   in
                                let uu____18700 = solve env1 wl'  in
                                (match uu____18700 with
                                 | Success (uu____18703,defer_to_tac,imps) ->
                                     let wl'1 =
                                       let uu___2740_18707 = wl'  in
                                       {
                                         attempting = [orig];
                                         wl_deferred =
                                           (uu___2740_18707.wl_deferred);
                                         wl_deferred_to_tac =
                                           (uu___2740_18707.wl_deferred_to_tac);
                                         ctr = (uu___2740_18707.ctr);
                                         defer_ok =
                                           (uu___2740_18707.defer_ok);
                                         smt_ok = (uu___2740_18707.smt_ok);
                                         umax_heuristic_ok =
                                           (uu___2740_18707.umax_heuristic_ok);
                                         tcenv = (uu___2740_18707.tcenv);
                                         wl_implicits =
                                           (uu___2740_18707.wl_implicits)
                                       }  in
                                     let uu____18708 = solve env1 wl'1  in
                                     (match uu____18708 with
                                      | Success
                                          (uu____18711,defer_to_tac',imps')
                                          ->
                                          (FStar_Syntax_Unionfind.commit tx;
                                           (let uu____18715 =
                                              extend_wl wl4
                                                (FStar_List.append
                                                   defer_to_tac defer_to_tac')
                                                (FStar_List.append imps imps')
                                               in
                                            FStar_Pervasives_Native.Some
                                              uu____18715))
                                      | Failed uu____18721 ->
                                          (FStar_Syntax_Unionfind.rollback tx;
                                           FStar_Pervasives_Native.None))
                                 | uu____18727 ->
                                     (FStar_Syntax_Unionfind.rollback tx;
                                      FStar_Pervasives_Native.None)))))
              in
           match t1t2_opt with
           | FStar_Pervasives_Native.None  ->
               FStar_Util.Inr FStar_Pervasives_Native.None
           | FStar_Pervasives_Native.Some (t1,t2) ->
               ((let uu____18750 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____18750
                 then
                   let uu____18755 = FStar_Syntax_Print.term_to_string t1  in
                   let uu____18757 = FStar_Syntax_Print.term_to_string t2  in
                   FStar_Util.print2 "Trying match heuristic for %s vs. %s\n"
                     uu____18755 uu____18757
                 else ());
                (let uu____18762 =
                   let uu____18783 =
                     let uu____18792 = FStar_Syntax_Util.unmeta t1  in
                     (s1, uu____18792)  in
                   let uu____18799 =
                     let uu____18808 = FStar_Syntax_Util.unmeta t2  in
                     (s2, uu____18808)  in
                   (uu____18783, uu____18799)  in
                 match uu____18762 with
                 | ((uu____18838,{
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_match
                                     (scrutinee,branches);
                                   FStar_Syntax_Syntax.pos = uu____18841;
                                   FStar_Syntax_Syntax.vars = uu____18842;_}),
                    (s,t)) ->
                     let uu____18913 =
                       let uu____18915 = is_flex scrutinee  in
                       Prims.op_Negation uu____18915  in
                     if uu____18913
                     then
                       ((let uu____18926 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____18926
                         then
                           let uu____18931 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____18931
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____18950 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18950
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____18965 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____18965
                           then
                             let uu____18970 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____18972 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____18970 uu____18972
                           else ());
                          (let pat_discriminates uu___28_18997 =
                             match uu___28_18997 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19013;
                                  FStar_Syntax_Syntax.p = uu____19014;_},FStar_Pervasives_Native.None
                                ,uu____19015) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19029;
                                  FStar_Syntax_Syntax.p = uu____19030;_},FStar_Pervasives_Native.None
                                ,uu____19031) -> true
                             | uu____19058 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____19161 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____19161 with
                                       | (uu____19163,uu____19164,t') ->
                                           let uu____19182 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____19182 with
                                            | (FullMatch ,uu____19194) ->
                                                true
                                            | (HeadMatch
                                               uu____19208,uu____19209) ->
                                                true
                                            | uu____19224 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____19261 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____19261
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____19272 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____19272 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____19360,uu____19361) ->
                                       branches1
                                   | uu____19506 -> branches  in
                                 let uu____19561 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____19570 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____19570 with
                                        | (p,uu____19574,uu____19575) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _19604  -> FStar_Util.Inr _19604)
                                   uu____19561))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____19634 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____19634 with
                                | (p,uu____19643,e) ->
                                    ((let uu____19662 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____19662
                                      then
                                        let uu____19667 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____19669 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____19667 uu____19669
                                      else ());
                                     (let uu____19674 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _19689  -> FStar_Util.Inr _19689)
                                        uu____19674)))))
                 | ((s,t),(uu____19692,{
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_match
                                           (scrutinee,branches);
                                         FStar_Syntax_Syntax.pos =
                                           uu____19695;
                                         FStar_Syntax_Syntax.vars =
                                           uu____19696;_}))
                     ->
                     let uu____19765 =
                       let uu____19767 = is_flex scrutinee  in
                       Prims.op_Negation uu____19767  in
                     if uu____19765
                     then
                       ((let uu____19778 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env1)
                             (FStar_Options.Other "Rel")
                            in
                         if uu____19778
                         then
                           let uu____19783 =
                             FStar_Syntax_Print.term_to_string scrutinee  in
                           FStar_Util.print1
                             "match head %s is not a flex term\n" uu____19783
                         else ());
                        FStar_Util.Inr FStar_Pervasives_Native.None)
                     else
                       if wl1.defer_ok
                       then
                         ((let uu____19802 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19802
                           then FStar_Util.print_string "Deferring ... \n"
                           else ());
                          FStar_Util.Inl "defer")
                       else
                         ((let uu____19817 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env1)
                               (FStar_Options.Other "Rel")
                              in
                           if uu____19817
                           then
                             let uu____19822 =
                               FStar_Syntax_Print.term_to_string scrutinee
                                in
                             let uu____19824 =
                               FStar_Syntax_Print.term_to_string t  in
                             FStar_Util.print2
                               "Heuristic applicable with scrutinee %s and other side = %s\n"
                               uu____19822 uu____19824
                           else ());
                          (let pat_discriminates uu___28_19849 =
                             match uu___28_19849 with
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_constant
                                    uu____19865;
                                  FStar_Syntax_Syntax.p = uu____19866;_},FStar_Pervasives_Native.None
                                ,uu____19867) -> true
                             | ({
                                  FStar_Syntax_Syntax.v =
                                    FStar_Syntax_Syntax.Pat_cons uu____19881;
                                  FStar_Syntax_Syntax.p = uu____19882;_},FStar_Pervasives_Native.None
                                ,uu____19883) -> true
                             | uu____19910 -> false  in
                           let head_matching_branch =
                             FStar_All.pipe_right branches
                               (FStar_Util.try_find
                                  (fun b  ->
                                     if pat_discriminates b
                                     then
                                       let uu____20013 =
                                         FStar_Syntax_Subst.open_branch b  in
                                       match uu____20013 with
                                       | (uu____20015,uu____20016,t') ->
                                           let uu____20034 =
                                             head_matches_delta env1 wl1 s t'
                                              in
                                           (match uu____20034 with
                                            | (FullMatch ,uu____20046) ->
                                                true
                                            | (HeadMatch
                                               uu____20060,uu____20061) ->
                                                true
                                            | uu____20076 -> false)
                                     else false))
                              in
                           match head_matching_branch with
                           | FStar_Pervasives_Native.None  ->
                               ((let uu____20113 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env1)
                                     (FStar_Options.Other "Rel")
                                    in
                                 if uu____20113
                                 then
                                   FStar_Util.print_string
                                     "No head_matching branch\n"
                                 else ());
                                (let try_branches =
                                   let uu____20124 =
                                     FStar_Util.prefix_until
                                       (fun b  ->
                                          Prims.op_Negation
                                            (pat_discriminates b)) branches
                                      in
                                   match uu____20124 with
                                   | FStar_Pervasives_Native.Some
                                       (branches1,uu____20212,uu____20213) ->
                                       branches1
                                   | uu____20358 -> branches  in
                                 let uu____20413 =
                                   FStar_Util.find_map try_branches
                                     (fun b  ->
                                        let uu____20422 =
                                          FStar_Syntax_Subst.open_branch b
                                           in
                                        match uu____20422 with
                                        | (p,uu____20426,uu____20427) ->
                                            try_solve_branch scrutinee p)
                                    in
                                 FStar_All.pipe_left
                                   (fun _20456  -> FStar_Util.Inr _20456)
                                   uu____20413))
                           | FStar_Pervasives_Native.Some b ->
                               let uu____20486 =
                                 FStar_Syntax_Subst.open_branch b  in
                               (match uu____20486 with
                                | (p,uu____20495,e) ->
                                    ((let uu____20514 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env1)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____20514
                                      then
                                        let uu____20519 =
                                          FStar_Syntax_Print.pat_to_string p
                                           in
                                        let uu____20521 =
                                          FStar_Syntax_Print.term_to_string e
                                           in
                                        FStar_Util.print2
                                          "Found head matching branch %s -> %s\n"
                                          uu____20519 uu____20521
                                      else ());
                                     (let uu____20526 =
                                        try_solve_branch scrutinee p  in
                                      FStar_All.pipe_left
                                        (fun _20541  -> FStar_Util.Inr _20541)
                                        uu____20526)))))
                 | uu____20542 ->
                     ((let uu____20564 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env1)
                           (FStar_Options.Other "Rel")
                          in
                       if uu____20564
                       then
                         let uu____20569 = FStar_Syntax_Print.tag_of_term t1
                            in
                         let uu____20571 = FStar_Syntax_Print.tag_of_term t2
                            in
                         FStar_Util.print2
                           "Heuristic not applicable: tag lhs=%s, rhs=%s\n"
                           uu____20569 uu____20571
                       else ());
                      FStar_Util.Inr FStar_Pervasives_Native.None)))
            in
         let rigid_rigid_delta env1 torig wl1 head1 head2 t1 t2 =
           let orig = FStar_TypeChecker_Common.TProb torig  in
           (let uu____20617 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                (FStar_Options.Other "RelDelta")
               in
            if uu____20617
            then
              let uu____20622 = FStar_Syntax_Print.tag_of_term t1  in
              let uu____20624 = FStar_Syntax_Print.tag_of_term t2  in
              let uu____20626 = FStar_Syntax_Print.term_to_string t1  in
              let uu____20628 = FStar_Syntax_Print.term_to_string t2  in
              FStar_Util.print4 "rigid_rigid_delta of %s-%s (%s, %s)\n"
                uu____20622 uu____20624 uu____20626 uu____20628
            else ());
           (let uu____20633 = head_matches_delta env1 wl1 t1 t2  in
            match uu____20633 with
            | (m,o) ->
                (match (m, o) with
                 | (MisMatch uu____20664,uu____20665) ->
                     let rec may_relate head3 =
                       let uu____20693 =
                         let uu____20694 = FStar_Syntax_Subst.compress head3
                            in
                         uu____20694.FStar_Syntax_Syntax.n  in
                       match uu____20693 with
                       | FStar_Syntax_Syntax.Tm_name uu____20698 -> true
                       | FStar_Syntax_Syntax.Tm_match uu____20700 -> true
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let uu____20725 =
                             FStar_TypeChecker_Env.delta_depth_of_fv env1 fv
                              in
                           (match uu____20725 with
                            | FStar_Syntax_Syntax.Delta_equational_at_level
                                uu____20727 -> true
                            | FStar_Syntax_Syntax.Delta_abstract uu____20730
                                ->
                                problem.FStar_TypeChecker_Common.relation =
                                  FStar_TypeChecker_Common.EQ
                            | uu____20731 -> false)
                       | FStar_Syntax_Syntax.Tm_ascribed
                           (t,uu____20734,uu____20735) -> may_relate t
                       | FStar_Syntax_Syntax.Tm_uinst (t,uu____20777) ->
                           may_relate t
                       | FStar_Syntax_Syntax.Tm_meta (t,uu____20783) ->
                           may_relate t
                       | uu____20788 -> false  in
                     let uu____20790 =
                       try_match_heuristic env1 orig wl1 t1 t2 o  in
                     (match uu____20790 with
                      | FStar_Util.Inl _defer_ok ->
                          let uu____20803 =
                            FStar_Thunk.mkv "delaying match heuristic"  in
                          giveup_or_defer1 orig uu____20803
                      | FStar_Util.Inr (FStar_Pervasives_Native.Some wl2) ->
                          solve env1 wl2
                      | FStar_Util.Inr (FStar_Pervasives_Native.None ) ->
                          let uu____20813 =
                            ((may_relate head1) || (may_relate head2)) &&
                              wl1.smt_ok
                             in
                          if uu____20813
                          then
                            let uu____20816 =
                              guard_of_prob env1 wl1 problem t1 t2  in
                            (match uu____20816 with
                             | (guard,wl2) ->
                                 let uu____20823 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some guard) []
                                     wl2
                                    in
                                 solve env1 uu____20823)
                          else
                            (let uu____20826 =
                               FStar_Thunk.mk
                                 (fun uu____20833  ->
                                    let uu____20834 =
                                      FStar_Syntax_Print.term_to_string head1
                                       in
                                    let uu____20836 =
                                      let uu____20838 =
                                        let uu____20842 =
                                          delta_depth_of_term env1 head1  in
                                        FStar_Util.bind_opt uu____20842
                                          (fun x  ->
                                             let uu____20849 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20849)
                                         in
                                      FStar_Util.dflt "" uu____20838  in
                                    let uu____20854 =
                                      FStar_Syntax_Print.term_to_string head2
                                       in
                                    let uu____20856 =
                                      let uu____20858 =
                                        let uu____20862 =
                                          delta_depth_of_term env1 head2  in
                                        FStar_Util.bind_opt uu____20862
                                          (fun x  ->
                                             let uu____20869 =
                                               FStar_Syntax_Print.delta_depth_to_string
                                                 x
                                                in
                                             FStar_Pervasives_Native.Some
                                               uu____20869)
                                         in
                                      FStar_Util.dflt "" uu____20858  in
                                    FStar_Util.format4
                                      "head mismatch (%s (%s) vs %s (%s))"
                                      uu____20834 uu____20836 uu____20854
                                      uu____20856)
                                in
                             giveup env1 uu____20826 orig))
                 | (HeadMatch (true ),uu____20875) when
                     problem.FStar_TypeChecker_Common.relation <>
                       FStar_TypeChecker_Common.EQ
                     ->
                     if wl1.smt_ok
                     then
                       let uu____20890 = guard_of_prob env1 wl1 problem t1 t2
                          in
                       (match uu____20890 with
                        | (guard,wl2) ->
                            let uu____20897 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some guard) [] wl2
                               in
                            solve env1 uu____20897)
                     else
                       (let uu____20900 =
                          FStar_Thunk.mk
                            (fun uu____20905  ->
                               let uu____20906 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____20908 =
                                 FStar_Syntax_Print.term_to_string t2  in
                               FStar_Util.format2
                                 "head mismatch for subtyping (%s vs %s)"
                                 uu____20906 uu____20908)
                           in
                        giveup env1 uu____20900 orig)
                 | (uu____20911,FStar_Pervasives_Native.Some (t11,t21)) ->
                     solve_t env1
                       (let uu___2922_20925 = problem  in
                        {
                          FStar_TypeChecker_Common.pid =
                            (uu___2922_20925.FStar_TypeChecker_Common.pid);
                          FStar_TypeChecker_Common.lhs = t11;
                          FStar_TypeChecker_Common.relation =
                            (uu___2922_20925.FStar_TypeChecker_Common.relation);
                          FStar_TypeChecker_Common.rhs = t21;
                          FStar_TypeChecker_Common.element =
                            (uu___2922_20925.FStar_TypeChecker_Common.element);
                          FStar_TypeChecker_Common.logical_guard =
                            (uu___2922_20925.FStar_TypeChecker_Common.logical_guard);
                          FStar_TypeChecker_Common.logical_guard_uvar =
                            (uu___2922_20925.FStar_TypeChecker_Common.logical_guard_uvar);
                          FStar_TypeChecker_Common.reason =
                            (uu___2922_20925.FStar_TypeChecker_Common.reason);
                          FStar_TypeChecker_Common.loc =
                            (uu___2922_20925.FStar_TypeChecker_Common.loc);
                          FStar_TypeChecker_Common.rank =
                            (uu___2922_20925.FStar_TypeChecker_Common.rank)
                        }) wl1
                 | (HeadMatch need_unif,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 need_unif torig wl1 t1 t2
                 | (FullMatch ,FStar_Pervasives_Native.None ) ->
                     rigid_heads_match env1 false torig wl1 t1 t2))
            in
         let orig = FStar_TypeChecker_Common.TProb problem  in
         def_check_prob "solve_t'.2" orig;
         (let uu____20952 =
            FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs
              problem.FStar_TypeChecker_Common.rhs
             in
          if uu____20952
          then
            let uu____20955 =
              solve_prob orig FStar_Pervasives_Native.None [] wl  in
            solve env uu____20955
          else
            (let t1 = problem.FStar_TypeChecker_Common.lhs  in
             let t2 = problem.FStar_TypeChecker_Common.rhs  in
             (let uu____20961 =
                let uu____20964 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20964  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t1"
                uu____20961 t1);
             (let uu____20983 =
                let uu____20986 = p_scope orig  in
                FStar_List.map FStar_Pervasives_Native.fst uu____20986  in
              FStar_TypeChecker_Env.def_check_closed_in (p_loc orig) "ref.t2"
                uu____20983 t2);
             (let uu____21005 =
                FStar_TypeChecker_Env.debug env (FStar_Options.Other "Rel")
                 in
              if uu____21005
              then
                let uu____21009 =
                  FStar_Util.string_of_int
                    problem.FStar_TypeChecker_Common.pid
                   in
                let uu____21011 =
                  let uu____21013 = FStar_Syntax_Print.tag_of_term t1  in
                  let uu____21015 =
                    let uu____21017 = FStar_Syntax_Print.term_to_string t1
                       in
                    Prims.op_Hat "::" uu____21017  in
                  Prims.op_Hat uu____21013 uu____21015  in
                let uu____21020 =
                  let uu____21022 = FStar_Syntax_Print.tag_of_term t2  in
                  let uu____21024 =
                    let uu____21026 = FStar_Syntax_Print.term_to_string t2
                       in
                    Prims.op_Hat "::" uu____21026  in
                  Prims.op_Hat uu____21022 uu____21024  in
                FStar_Util.print4 "Attempting %s (%s vs %s); rel = (%s)\n"
                  uu____21009 uu____21011 uu____21020
                  (rel_to_string problem.FStar_TypeChecker_Common.relation)
              else ());
             (let r = FStar_TypeChecker_Env.get_range env  in
              match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n))
              with
              | (FStar_Syntax_Syntax.Tm_delayed uu____21033,uu____21034) ->
                  failwith "Impossible: terms were not compressed"
              | (uu____21050,FStar_Syntax_Syntax.Tm_delayed uu____21051) ->
                  failwith "Impossible: terms were not compressed"
              | (FStar_Syntax_Syntax.Tm_ascribed uu____21067,uu____21068) ->
                  let uu____21095 =
                    let uu___2953_21096 = problem  in
                    let uu____21097 = FStar_Syntax_Util.unascribe t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2953_21096.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21097;
                      FStar_TypeChecker_Common.relation =
                        (uu___2953_21096.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2953_21096.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2953_21096.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2953_21096.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2953_21096.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2953_21096.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2953_21096.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2953_21096.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21095 wl
              | (FStar_Syntax_Syntax.Tm_meta uu____21098,uu____21099) ->
                  let uu____21106 =
                    let uu___2959_21107 = problem  in
                    let uu____21108 = FStar_Syntax_Util.unmeta t1  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2959_21107.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs = uu____21108;
                      FStar_TypeChecker_Common.relation =
                        (uu___2959_21107.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs =
                        (uu___2959_21107.FStar_TypeChecker_Common.rhs);
                      FStar_TypeChecker_Common.element =
                        (uu___2959_21107.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2959_21107.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2959_21107.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2959_21107.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2959_21107.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2959_21107.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21106 wl
              | (uu____21109,FStar_Syntax_Syntax.Tm_ascribed uu____21110) ->
                  let uu____21137 =
                    let uu___2965_21138 = problem  in
                    let uu____21139 = FStar_Syntax_Util.unascribe t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2965_21138.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2965_21138.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2965_21138.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21139;
                      FStar_TypeChecker_Common.element =
                        (uu___2965_21138.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2965_21138.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2965_21138.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2965_21138.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2965_21138.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2965_21138.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21137 wl
              | (uu____21140,FStar_Syntax_Syntax.Tm_meta uu____21141) ->
                  let uu____21148 =
                    let uu___2971_21149 = problem  in
                    let uu____21150 = FStar_Syntax_Util.unmeta t2  in
                    {
                      FStar_TypeChecker_Common.pid =
                        (uu___2971_21149.FStar_TypeChecker_Common.pid);
                      FStar_TypeChecker_Common.lhs =
                        (uu___2971_21149.FStar_TypeChecker_Common.lhs);
                      FStar_TypeChecker_Common.relation =
                        (uu___2971_21149.FStar_TypeChecker_Common.relation);
                      FStar_TypeChecker_Common.rhs = uu____21150;
                      FStar_TypeChecker_Common.element =
                        (uu___2971_21149.FStar_TypeChecker_Common.element);
                      FStar_TypeChecker_Common.logical_guard =
                        (uu___2971_21149.FStar_TypeChecker_Common.logical_guard);
                      FStar_TypeChecker_Common.logical_guard_uvar =
                        (uu___2971_21149.FStar_TypeChecker_Common.logical_guard_uvar);
                      FStar_TypeChecker_Common.reason =
                        (uu___2971_21149.FStar_TypeChecker_Common.reason);
                      FStar_TypeChecker_Common.loc =
                        (uu___2971_21149.FStar_TypeChecker_Common.loc);
                      FStar_TypeChecker_Common.rank =
                        (uu___2971_21149.FStar_TypeChecker_Common.rank)
                    }  in
                  solve_t' env uu____21148 wl
              | (FStar_Syntax_Syntax.Tm_quoted
                 (t11,uu____21152),FStar_Syntax_Syntax.Tm_quoted
                 (t21,uu____21154)) ->
                  let uu____21163 =
                    solve_prob orig FStar_Pervasives_Native.None [] wl  in
                  solve env uu____21163
              | (FStar_Syntax_Syntax.Tm_bvar uu____21164,uu____21165) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (uu____21167,FStar_Syntax_Syntax.Tm_bvar uu____21168) ->
                  failwith
                    "Only locally nameless! We should never see a de Bruijn variable"
              | (FStar_Syntax_Syntax.Tm_type u1,FStar_Syntax_Syntax.Tm_type
                 u2) -> solve_one_universe_eq env orig u1 u2 wl
              | (FStar_Syntax_Syntax.Tm_arrow
                 (bs1,c1),FStar_Syntax_Syntax.Tm_arrow (bs2,c2)) ->
                  let mk_c c uu___29_21238 =
                    match uu___29_21238 with
                    | [] -> c
                    | bs ->
                        let uu____21266 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (bs, c))
                            FStar_Pervasives_Native.None
                            c.FStar_Syntax_Syntax.pos
                           in
                        FStar_Syntax_Syntax.mk_Total uu____21266
                     in
                  let uu____21277 =
                    match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2))  in
                  (match uu____21277 with
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
                                    let uu____21426 =
                                      FStar_Options.use_eq_at_higher_order ()
                                       in
                                    if uu____21426
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
                  let mk_t t l uu___30_21515 =
                    match uu___30_21515 with
                    | [] -> t
                    | bs ->
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_abs (bs, t, l))
                          FStar_Pervasives_Native.None
                          t.FStar_Syntax_Syntax.pos
                     in
                  let uu____21557 =
                    match_num_binders (bs1, (mk_t tbody1 lopt1))
                      (bs2, (mk_t tbody2 lopt2))
                     in
                  (match uu____21557 with
                   | ((bs11,tbody11),(bs21,tbody21)) ->
                       solve_binders env bs11 bs21 orig wl
                         (fun wl1  ->
                            fun scope  ->
                              fun env1  ->
                                fun subst1  ->
                                  let uu____21702 =
                                    FStar_Syntax_Subst.subst subst1 tbody11
                                     in
                                  let uu____21703 =
                                    FStar_Syntax_Subst.subst subst1 tbody21
                                     in
                                  mk_t_problem wl1 scope orig uu____21702
                                    problem.FStar_TypeChecker_Common.relation
                                    uu____21703 FStar_Pervasives_Native.None
                                    "lambda co-domain"))
              | (FStar_Syntax_Syntax.Tm_abs uu____21705,uu____21706) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____21737 -> true
                    | uu____21757 -> false  in
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
                      (let uu____21817 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3073_21825 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3073_21825.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3073_21825.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3073_21825.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3073_21825.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3073_21825.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3073_21825.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3073_21825.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3073_21825.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3073_21825.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3073_21825.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3073_21825.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3073_21825.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3073_21825.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3073_21825.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3073_21825.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3073_21825.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3073_21825.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3073_21825.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3073_21825.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3073_21825.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3073_21825.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3073_21825.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3073_21825.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3073_21825.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3073_21825.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3073_21825.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3073_21825.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3073_21825.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3073_21825.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3073_21825.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3073_21825.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3073_21825.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3073_21825.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3073_21825.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3073_21825.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3073_21825.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3073_21825.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3073_21825.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3073_21825.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3073_21825.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3073_21825.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3073_21825.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3073_21825.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3073_21825.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3073_21825.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____21817 with
                       | (uu____21830,ty,uu____21832) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____21841 =
                                 let uu____21842 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____21842.FStar_Syntax_Syntax.n  in
                               match uu____21841 with
                               | FStar_Syntax_Syntax.Tm_refine uu____21845 ->
                                   let uu____21852 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____21852
                               | uu____21853 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____21856 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____21856
                             then
                               let uu____21861 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____21863 =
                                 let uu____21865 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____21865
                                  in
                               let uu____21866 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____21861 uu____21863 uu____21866
                             else ());
                            r1))
                     in
                  let uu____21871 =
                    let uu____21888 = maybe_eta t1  in
                    let uu____21895 = maybe_eta t2  in
                    (uu____21888, uu____21895)  in
                  (match uu____21871 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3094_21937 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3094_21937.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3094_21937.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3094_21937.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3094_21937.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3094_21937.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3094_21937.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3094_21937.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3094_21937.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____21958 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____21958
                       then
                         let uu____21961 = destruct_flex_t not_abs wl  in
                         (match uu____21961 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_21978 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_21978.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_21978.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_21978.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_21978.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_21978.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_21978.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_21978.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_21978.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____21981 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____21981 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22004 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22004
                       then
                         let uu____22007 = destruct_flex_t not_abs wl  in
                         (match uu____22007 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_22024 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_22024.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_22024.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_22024.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_22024.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_22024.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_22024.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_22024.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_22024.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22027 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22027 orig))
                   | uu____22030 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (uu____22048,FStar_Syntax_Syntax.Tm_abs uu____22049) ->
                  let is_abs t =
                    match t.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Tm_abs uu____22080 -> true
                    | uu____22100 -> false  in
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
                      (let uu____22160 =
                         env.FStar_TypeChecker_Env.type_of
                           (let uu___3073_22168 = env  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___3073_22168.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___3073_22168.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___3073_22168.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___3073_22168.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_sig =
                                (uu___3073_22168.FStar_TypeChecker_Env.gamma_sig);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___3073_22168.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___3073_22168.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                FStar_Pervasives_Native.None;
                              FStar_TypeChecker_Env.sigtab =
                                (uu___3073_22168.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.attrtab =
                                (uu___3073_22168.FStar_TypeChecker_Env.attrtab);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___3073_22168.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___3073_22168.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___3073_22168.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___3073_22168.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___3073_22168.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___3073_22168.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___3073_22168.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.use_eq_strict =
                                (uu___3073_22168.FStar_TypeChecker_Env.use_eq_strict);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___3073_22168.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___3073_22168.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___3073_22168.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.phase1 =
                                (uu___3073_22168.FStar_TypeChecker_Env.phase1);
                              FStar_TypeChecker_Env.failhard =
                                (uu___3073_22168.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___3073_22168.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.uvar_subtyping =
                                (uu___3073_22168.FStar_TypeChecker_Env.uvar_subtyping);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___3073_22168.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___3073_22168.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___3073_22168.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.check_type_of =
                                (uu___3073_22168.FStar_TypeChecker_Env.check_type_of);
                              FStar_TypeChecker_Env.use_bv_sorts = true;
                              FStar_TypeChecker_Env.qtbl_name_and_index =
                                (uu___3073_22168.FStar_TypeChecker_Env.qtbl_name_and_index);
                              FStar_TypeChecker_Env.normalized_eff_names =
                                (uu___3073_22168.FStar_TypeChecker_Env.normalized_eff_names);
                              FStar_TypeChecker_Env.fv_delta_depths =
                                (uu___3073_22168.FStar_TypeChecker_Env.fv_delta_depths);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___3073_22168.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth_hook =
                                (uu___3073_22168.FStar_TypeChecker_Env.synth_hook);
                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                =
                                (uu___3073_22168.FStar_TypeChecker_Env.try_solve_implicits_hook);
                              FStar_TypeChecker_Env.splice =
                                (uu___3073_22168.FStar_TypeChecker_Env.splice);
                              FStar_TypeChecker_Env.mpreprocess =
                                (uu___3073_22168.FStar_TypeChecker_Env.mpreprocess);
                              FStar_TypeChecker_Env.postprocess =
                                (uu___3073_22168.FStar_TypeChecker_Env.postprocess);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___3073_22168.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___3073_22168.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___3073_22168.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___3073_22168.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.nbe =
                                (uu___3073_22168.FStar_TypeChecker_Env.nbe);
                              FStar_TypeChecker_Env.strict_args_tab =
                                (uu___3073_22168.FStar_TypeChecker_Env.strict_args_tab);
                              FStar_TypeChecker_Env.erasable_types_tab =
                                (uu___3073_22168.FStar_TypeChecker_Env.erasable_types_tab);
                              FStar_TypeChecker_Env.enable_defer_to_tac =
                                (uu___3073_22168.FStar_TypeChecker_Env.enable_defer_to_tac)
                            }) t
                          in
                       match uu____22160 with
                       | (uu____22173,ty,uu____22175) ->
                           let ty1 =
                             let rec aux ty1 =
                               let ty2 =
                                 FStar_TypeChecker_Normalize.unfold_whnf env
                                   ty1
                                  in
                               let uu____22184 =
                                 let uu____22185 =
                                   FStar_Syntax_Subst.compress ty2  in
                                 uu____22185.FStar_Syntax_Syntax.n  in
                               match uu____22184 with
                               | FStar_Syntax_Syntax.Tm_refine uu____22188 ->
                                   let uu____22195 =
                                     FStar_Syntax_Util.unrefine ty2  in
                                   aux uu____22195
                               | uu____22196 -> ty2  in
                             aux ty  in
                           let r1 =
                             FStar_TypeChecker_Normalize.eta_expand_with_type
                               env t ty1
                              in
                           ((let uu____22199 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug wl.tcenv)
                                 (FStar_Options.Other "Rel")
                                in
                             if uu____22199
                             then
                               let uu____22204 =
                                 FStar_Syntax_Print.term_to_string t  in
                               let uu____22206 =
                                 let uu____22208 =
                                   FStar_TypeChecker_Normalize.unfold_whnf
                                     env ty1
                                    in
                                 FStar_Syntax_Print.term_to_string
                                   uu____22208
                                  in
                               let uu____22209 =
                                 FStar_Syntax_Print.term_to_string r1  in
                               FStar_Util.print3
                                 "force_eta of (%s) at type (%s) = %s\n"
                                 uu____22204 uu____22206 uu____22209
                             else ());
                            r1))
                     in
                  let uu____22214 =
                    let uu____22231 = maybe_eta t1  in
                    let uu____22238 = maybe_eta t2  in
                    (uu____22231, uu____22238)  in
                  (match uu____22214 with
                   | (FStar_Util.Inl t11,FStar_Util.Inl t21) ->
                       solve_t env
                         (let uu___3094_22280 = problem  in
                          {
                            FStar_TypeChecker_Common.pid =
                              (uu___3094_22280.FStar_TypeChecker_Common.pid);
                            FStar_TypeChecker_Common.lhs = t11;
                            FStar_TypeChecker_Common.relation =
                              (uu___3094_22280.FStar_TypeChecker_Common.relation);
                            FStar_TypeChecker_Common.rhs = t21;
                            FStar_TypeChecker_Common.element =
                              (uu___3094_22280.FStar_TypeChecker_Common.element);
                            FStar_TypeChecker_Common.logical_guard =
                              (uu___3094_22280.FStar_TypeChecker_Common.logical_guard);
                            FStar_TypeChecker_Common.logical_guard_uvar =
                              (uu___3094_22280.FStar_TypeChecker_Common.logical_guard_uvar);
                            FStar_TypeChecker_Common.reason =
                              (uu___3094_22280.FStar_TypeChecker_Common.reason);
                            FStar_TypeChecker_Common.loc =
                              (uu___3094_22280.FStar_TypeChecker_Common.loc);
                            FStar_TypeChecker_Common.rank =
                              (uu___3094_22280.FStar_TypeChecker_Common.rank)
                          }) wl
                   | (FStar_Util.Inl t_abs,FStar_Util.Inr not_abs) ->
                       let uu____22301 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22301
                       then
                         let uu____22304 = destruct_flex_t not_abs wl  in
                         (match uu____22304 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_22321 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_22321.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_22321.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_22321.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_22321.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_22321.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_22321.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_22321.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_22321.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22324 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22324 orig))
                   | (FStar_Util.Inr not_abs,FStar_Util.Inl t_abs) ->
                       let uu____22347 =
                         (is_flex not_abs) &&
                           ((p_rel orig) = FStar_TypeChecker_Common.EQ)
                          in
                       if uu____22347
                       then
                         let uu____22350 = destruct_flex_t not_abs wl  in
                         (match uu____22350 with
                          | (flex,wl1) ->
                              solve_t_flex_rigid_eq env orig wl1 flex t_abs)
                       else
                         (let t11 = force_eta t1  in
                          let t21 = force_eta t2  in
                          if (is_abs t11) && (is_abs t21)
                          then
                            solve_t env
                              (let uu___3111_22367 = problem  in
                               {
                                 FStar_TypeChecker_Common.pid =
                                   (uu___3111_22367.FStar_TypeChecker_Common.pid);
                                 FStar_TypeChecker_Common.lhs = t11;
                                 FStar_TypeChecker_Common.relation =
                                   (uu___3111_22367.FStar_TypeChecker_Common.relation);
                                 FStar_TypeChecker_Common.rhs = t21;
                                 FStar_TypeChecker_Common.element =
                                   (uu___3111_22367.FStar_TypeChecker_Common.element);
                                 FStar_TypeChecker_Common.logical_guard =
                                   (uu___3111_22367.FStar_TypeChecker_Common.logical_guard);
                                 FStar_TypeChecker_Common.logical_guard_uvar
                                   =
                                   (uu___3111_22367.FStar_TypeChecker_Common.logical_guard_uvar);
                                 FStar_TypeChecker_Common.reason =
                                   (uu___3111_22367.FStar_TypeChecker_Common.reason);
                                 FStar_TypeChecker_Common.loc =
                                   (uu___3111_22367.FStar_TypeChecker_Common.loc);
                                 FStar_TypeChecker_Common.rank =
                                   (uu___3111_22367.FStar_TypeChecker_Common.rank)
                               }) wl
                          else
                            (let uu____22370 =
                               FStar_Thunk.mkv
                                 "head tag mismatch: RHS is an abstraction"
                                in
                             giveup env uu____22370 orig))
                   | uu____22373 ->
                       failwith
                         "Impossible: at least one side is an abstraction")
              | (FStar_Syntax_Syntax.Tm_refine
                 (x1,phi1),FStar_Syntax_Syntax.Tm_refine (x2,phi2)) ->
                  let uu____22403 =
                    let uu____22408 =
                      head_matches_delta env wl x1.FStar_Syntax_Syntax.sort
                        x2.FStar_Syntax_Syntax.sort
                       in
                    match uu____22408 with
                    | (FullMatch ,FStar_Pervasives_Native.Some (t11,t21)) ->
                        ((let uu___3134_22436 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3134_22436.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3134_22436.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3136_22438 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3136_22438.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3136_22438.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | (HeadMatch uu____22439,FStar_Pervasives_Native.Some
                       (t11,t21)) ->
                        ((let uu___3134_22454 = x1  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___3134_22454.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___3134_22454.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t11
                          }),
                          (let uu___3136_22456 = x2  in
                           {
                             FStar_Syntax_Syntax.ppname =
                               (uu___3136_22456.FStar_Syntax_Syntax.ppname);
                             FStar_Syntax_Syntax.index =
                               (uu___3136_22456.FStar_Syntax_Syntax.index);
                             FStar_Syntax_Syntax.sort = t21
                           }))
                    | uu____22457 -> (x1, x2)  in
                  (match uu____22403 with
                   | (x11,x21) ->
                       let t11 = FStar_Syntax_Util.refine x11 phi1  in
                       let t21 = FStar_Syntax_Util.refine x21 phi2  in
                       let uu____22476 = as_refinement false env t11  in
                       (match uu____22476 with
                        | (x12,phi11) ->
                            let uu____22484 = as_refinement false env t21  in
                            (match uu____22484 with
                             | (x22,phi21) ->
                                 ((let uu____22493 =
                                     FStar_TypeChecker_Env.debug env
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____22493
                                   then
                                     ((let uu____22498 =
                                         FStar_Syntax_Print.bv_to_string x12
                                          in
                                       let uu____22500 =
                                         FStar_Syntax_Print.term_to_string
                                           x12.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22502 =
                                         FStar_Syntax_Print.term_to_string
                                           phi11
                                          in
                                       FStar_Util.print3
                                         "ref1 = (%s):(%s){%s}\n" uu____22498
                                         uu____22500 uu____22502);
                                      (let uu____22505 =
                                         FStar_Syntax_Print.bv_to_string x22
                                          in
                                       let uu____22507 =
                                         FStar_Syntax_Print.term_to_string
                                           x22.FStar_Syntax_Syntax.sort
                                          in
                                       let uu____22509 =
                                         FStar_Syntax_Print.term_to_string
                                           phi21
                                          in
                                       FStar_Util.print3
                                         "ref2 = (%s):(%s){%s}\n" uu____22505
                                         uu____22507 uu____22509))
                                   else ());
                                  (let uu____22514 =
                                     mk_t_problem wl [] orig
                                       x12.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.relation
                                       x22.FStar_Syntax_Syntax.sort
                                       problem.FStar_TypeChecker_Common.element
                                       "refinement base type"
                                      in
                                   match uu____22514 with
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
                                         let uu____22585 = imp phi13 phi23
                                            in
                                         FStar_All.pipe_right uu____22585
                                           (guard_on_element wl1 problem x13)
                                          in
                                       let fallback uu____22597 =
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
                                         (let uu____22610 =
                                            let uu____22613 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22613
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.1" uu____22610
                                            (p_guard base_prob));
                                         (let uu____22632 =
                                            let uu____22635 = p_scope orig
                                               in
                                            FStar_List.map
                                              FStar_Pervasives_Native.fst
                                              uu____22635
                                             in
                                          FStar_TypeChecker_Env.def_check_closed_in
                                            (p_loc orig) "ref.2" uu____22632
                                            impl);
                                         (let wl2 =
                                            solve_prob orig
                                              (FStar_Pervasives_Native.Some
                                                 guard) [] wl1
                                             in
                                          let uu____22654 =
                                            attempt [base_prob] wl2  in
                                          solve env1 uu____22654)
                                          in
                                       let has_uvars =
                                         (let uu____22659 =
                                            let uu____22661 =
                                              FStar_Syntax_Free.uvars phi12
                                               in
                                            FStar_Util.set_is_empty
                                              uu____22661
                                             in
                                          Prims.op_Negation uu____22659) ||
                                           (let uu____22665 =
                                              let uu____22667 =
                                                FStar_Syntax_Free.uvars phi22
                                                 in
                                              FStar_Util.set_is_empty
                                                uu____22667
                                               in
                                            Prims.op_Negation uu____22665)
                                          in
                                       if
                                         (problem.FStar_TypeChecker_Common.relation
                                            = FStar_TypeChecker_Common.EQ)
                                           ||
                                           ((Prims.op_Negation
                                               env1.FStar_TypeChecker_Env.uvar_subtyping)
                                              && has_uvars)
                                       then
                                         let uu____22671 =
                                           let uu____22676 =
                                             let uu____22685 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 x13
                                                in
                                             [uu____22685]  in
                                           mk_t_problem wl1 uu____22676 orig
                                             phi12
                                             FStar_TypeChecker_Common.EQ
                                             phi22
                                             FStar_Pervasives_Native.None
                                             "refinement formula"
                                            in
                                         (match uu____22671 with
                                          | (ref_prob,wl2) ->
                                              let tx =
                                                FStar_Syntax_Unionfind.new_transaction
                                                  ()
                                                 in
                                              let uu____22708 =
                                                solve env1
                                                  (let uu___3179_22710 = wl2
                                                      in
                                                   {
                                                     attempting = [ref_prob];
                                                     wl_deferred = [];
                                                     wl_deferred_to_tac =
                                                       (uu___3179_22710.wl_deferred_to_tac);
                                                     ctr =
                                                       (uu___3179_22710.ctr);
                                                     defer_ok = false;
                                                     smt_ok =
                                                       (uu___3179_22710.smt_ok);
                                                     umax_heuristic_ok =
                                                       (uu___3179_22710.umax_heuristic_ok);
                                                     tcenv =
                                                       (uu___3179_22710.tcenv);
                                                     wl_implicits =
                                                       (uu___3179_22710.wl_implicits)
                                                   })
                                                 in
                                              (match uu____22708 with
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
                                                   (uu____22725,defer_to_tac,uu____22727)
                                                   ->
                                                   (FStar_Syntax_Unionfind.commit
                                                      tx;
                                                    (let guard =
                                                       let uu____22732 =
                                                         FStar_All.pipe_right
                                                           (p_guard ref_prob)
                                                           (guard_on_element
                                                              wl2 problem x13)
                                                          in
                                                       FStar_Syntax_Util.mk_conj
                                                         (p_guard base_prob)
                                                         uu____22732
                                                        in
                                                     let wl3 =
                                                       solve_prob orig
                                                         (FStar_Pervasives_Native.Some
                                                            guard) [] wl2
                                                        in
                                                     let wl4 =
                                                       let uu___3195_22741 =
                                                         wl3  in
                                                       {
                                                         attempting =
                                                           (uu___3195_22741.attempting);
                                                         wl_deferred =
                                                           (uu___3195_22741.wl_deferred);
                                                         wl_deferred_to_tac =
                                                           (uu___3195_22741.wl_deferred_to_tac);
                                                         ctr =
                                                           (wl3.ctr +
                                                              Prims.int_one);
                                                         defer_ok =
                                                           (uu___3195_22741.defer_ok);
                                                         smt_ok =
                                                           (uu___3195_22741.smt_ok);
                                                         umax_heuristic_ok =
                                                           (uu___3195_22741.umax_heuristic_ok);
                                                         tcenv =
                                                           (uu___3195_22741.tcenv);
                                                         wl_implicits =
                                                           (uu___3195_22741.wl_implicits)
                                                       }  in
                                                     let wl5 =
                                                       extend_wl wl4
                                                         defer_to_tac []
                                                        in
                                                     let uu____22744 =
                                                       attempt [base_prob]
                                                         wl5
                                                        in
                                                     solve env1 uu____22744))))
                                       else fallback ())))))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22747,FStar_Syntax_Syntax.Tm_uvar uu____22748) ->
                  let uu____22773 = destruct_flex_t t1 wl  in
                  (match uu____22773 with
                   | (f1,wl1) ->
                       let uu____22780 = destruct_flex_t t2 wl1  in
                       (match uu____22780 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22787;
                    FStar_Syntax_Syntax.pos = uu____22788;
                    FStar_Syntax_Syntax.vars = uu____22789;_},uu____22790),FStar_Syntax_Syntax.Tm_uvar
                 uu____22791) ->
                  let uu____22840 = destruct_flex_t t1 wl  in
                  (match uu____22840 with
                   | (f1,wl1) ->
                       let uu____22847 = destruct_flex_t t2 wl1  in
                       (match uu____22847 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____22854,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22855;
                    FStar_Syntax_Syntax.pos = uu____22856;
                    FStar_Syntax_Syntax.vars = uu____22857;_},uu____22858))
                  ->
                  let uu____22907 = destruct_flex_t t1 wl  in
                  (match uu____22907 with
                   | (f1,wl1) ->
                       let uu____22914 = destruct_flex_t t2 wl1  in
                       (match uu____22914 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22921;
                    FStar_Syntax_Syntax.pos = uu____22922;
                    FStar_Syntax_Syntax.vars = uu____22923;_},uu____22924),FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____22925;
                    FStar_Syntax_Syntax.pos = uu____22926;
                    FStar_Syntax_Syntax.vars = uu____22927;_},uu____22928))
                  ->
                  let uu____23001 = destruct_flex_t t1 wl  in
                  (match uu____23001 with
                   | (f1,wl1) ->
                       let uu____23008 = destruct_flex_t t2 wl1  in
                       (match uu____23008 with
                        | (f2,wl2) -> solve_t_flex_flex env orig wl2 f1 f2))
              | (FStar_Syntax_Syntax.Tm_uvar uu____23015,uu____23016) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23029 = destruct_flex_t t1 wl  in
                  (match uu____23029 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23036;
                    FStar_Syntax_Syntax.pos = uu____23037;
                    FStar_Syntax_Syntax.vars = uu____23038;_},uu____23039),uu____23040)
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  ->
                  let uu____23077 = destruct_flex_t t1 wl  in
                  (match uu____23077 with
                   | (f1,wl1) -> solve_t_flex_rigid_eq env orig wl1 f1 t2)
              | (uu____23084,FStar_Syntax_Syntax.Tm_uvar uu____23085) when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (uu____23098,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23099;
                    FStar_Syntax_Syntax.pos = uu____23100;
                    FStar_Syntax_Syntax.vars = uu____23101;_},uu____23102))
                  when
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                  -> solve_t env (invert problem) wl
              | (FStar_Syntax_Syntax.Tm_uvar
                 uu____23139,FStar_Syntax_Syntax.Tm_arrow uu____23140) ->
                  solve_t' env
                    (let uu___3296_23168 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3296_23168.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3296_23168.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3296_23168.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3296_23168.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3296_23168.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3296_23168.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3296_23168.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3296_23168.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3296_23168.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23169;
                    FStar_Syntax_Syntax.pos = uu____23170;
                    FStar_Syntax_Syntax.vars = uu____23171;_},uu____23172),FStar_Syntax_Syntax.Tm_arrow
                 uu____23173) ->
                  solve_t' env
                    (let uu___3296_23225 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3296_23225.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3296_23225.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         FStar_TypeChecker_Common.EQ;
                       FStar_TypeChecker_Common.rhs =
                         (uu___3296_23225.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3296_23225.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3296_23225.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3296_23225.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3296_23225.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3296_23225.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3296_23225.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23226,FStar_Syntax_Syntax.Tm_uvar uu____23227) ->
                  let uu____23240 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23240
              | (uu____23241,FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23242;
                    FStar_Syntax_Syntax.pos = uu____23243;
                    FStar_Syntax_Syntax.vars = uu____23244;_},uu____23245))
                  ->
                  let uu____23282 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23282
              | (FStar_Syntax_Syntax.Tm_uvar uu____23283,uu____23284) ->
                  let uu____23297 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23297
              | (FStar_Syntax_Syntax.Tm_app
                 ({
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                      uu____23298;
                    FStar_Syntax_Syntax.pos = uu____23299;
                    FStar_Syntax_Syntax.vars = uu____23300;_},uu____23301),uu____23302)
                  ->
                  let uu____23339 =
                    attempt [FStar_TypeChecker_Common.TProb problem] wl  in
                  solve env uu____23339
              | (FStar_Syntax_Syntax.Tm_refine uu____23340,uu____23341) ->
                  let t21 =
                    let uu____23349 = base_and_refinement env t2  in
                    FStar_All.pipe_left force_refinement uu____23349  in
                  solve_t env
                    (let uu___3331_23375 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3331_23375.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs =
                         (uu___3331_23375.FStar_TypeChecker_Common.lhs);
                       FStar_TypeChecker_Common.relation =
                         (uu___3331_23375.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs = t21;
                       FStar_TypeChecker_Common.element =
                         (uu___3331_23375.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3331_23375.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3331_23375.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3331_23375.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3331_23375.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3331_23375.FStar_TypeChecker_Common.rank)
                     }) wl
              | (uu____23376,FStar_Syntax_Syntax.Tm_refine uu____23377) ->
                  let t11 =
                    let uu____23385 = base_and_refinement env t1  in
                    FStar_All.pipe_left force_refinement uu____23385  in
                  solve_t env
                    (let uu___3338_23411 = problem  in
                     {
                       FStar_TypeChecker_Common.pid =
                         (uu___3338_23411.FStar_TypeChecker_Common.pid);
                       FStar_TypeChecker_Common.lhs = t11;
                       FStar_TypeChecker_Common.relation =
                         (uu___3338_23411.FStar_TypeChecker_Common.relation);
                       FStar_TypeChecker_Common.rhs =
                         (uu___3338_23411.FStar_TypeChecker_Common.rhs);
                       FStar_TypeChecker_Common.element =
                         (uu___3338_23411.FStar_TypeChecker_Common.element);
                       FStar_TypeChecker_Common.logical_guard =
                         (uu___3338_23411.FStar_TypeChecker_Common.logical_guard);
                       FStar_TypeChecker_Common.logical_guard_uvar =
                         (uu___3338_23411.FStar_TypeChecker_Common.logical_guard_uvar);
                       FStar_TypeChecker_Common.reason =
                         (uu___3338_23411.FStar_TypeChecker_Common.reason);
                       FStar_TypeChecker_Common.loc =
                         (uu___3338_23411.FStar_TypeChecker_Common.loc);
                       FStar_TypeChecker_Common.rank =
                         (uu___3338_23411.FStar_TypeChecker_Common.rank)
                     }) wl
              | (FStar_Syntax_Syntax.Tm_match
                 (s1,brs1),FStar_Syntax_Syntax.Tm_match (s2,brs2)) ->
                  let by_smt uu____23493 =
                    let uu____23494 = guard_of_prob env wl problem t1 t2  in
                    match uu____23494 with
                    | (guard,wl1) ->
                        let uu____23501 =
                          solve_prob orig
                            (FStar_Pervasives_Native.Some guard) [] wl1
                           in
                        solve env uu____23501
                     in
                  let rec solve_branches wl1 brs11 brs21 =
                    match (brs11, brs21) with
                    | (br1::rs1,br2::rs2) ->
                        let uu____23720 = br1  in
                        (match uu____23720 with
                         | (p1,w1,uu____23749) ->
                             let uu____23766 = br2  in
                             (match uu____23766 with
                              | (p2,w2,uu____23789) ->
                                  let uu____23794 =
                                    let uu____23796 =
                                      FStar_Syntax_Syntax.eq_pat p1 p2  in
                                    Prims.op_Negation uu____23796  in
                                  if uu____23794
                                  then FStar_Pervasives_Native.None
                                  else
                                    (let uu____23823 =
                                       FStar_Syntax_Subst.open_branch' br1
                                        in
                                     match uu____23823 with
                                     | ((p11,w11,e1),s) ->
                                         let uu____23860 = br2  in
                                         (match uu____23860 with
                                          | (p21,w21,e2) ->
                                              let w22 =
                                                FStar_Util.map_opt w21
                                                  (FStar_Syntax_Subst.subst s)
                                                 in
                                              let e21 =
                                                FStar_Syntax_Subst.subst s e2
                                                 in
                                              let scope =
                                                let uu____23893 =
                                                  FStar_Syntax_Syntax.pat_bvs
                                                    p11
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.mk_binder)
                                                  uu____23893
                                                 in
                                              let uu____23898 =
                                                match (w11, w22) with
                                                | (FStar_Pervasives_Native.Some
                                                   uu____23929,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.Some
                                                   uu____23950) ->
                                                    FStar_Pervasives_Native.None
                                                | (FStar_Pervasives_Native.None
                                                   ,FStar_Pervasives_Native.None
                                                   ) ->
                                                    FStar_Pervasives_Native.Some
                                                      ([], wl1)
                                                | (FStar_Pervasives_Native.Some
                                                   w12,FStar_Pervasives_Native.Some
                                                   w23) ->
                                                    let uu____24009 =
                                                      mk_t_problem wl1 scope
                                                        orig w12
                                                        FStar_TypeChecker_Common.EQ
                                                        w23
                                                        FStar_Pervasives_Native.None
                                                        "when clause"
                                                       in
                                                    (match uu____24009 with
                                                     | (p,wl2) ->
                                                         FStar_Pervasives_Native.Some
                                                           ([(scope, p)],
                                                             wl2))
                                                 in
                                              FStar_Util.bind_opt uu____23898
                                                (fun uu____24081  ->
                                                   match uu____24081 with
                                                   | (wprobs,wl2) ->
                                                       let uu____24118 =
                                                         mk_t_problem wl2
                                                           scope orig e1
                                                           FStar_TypeChecker_Common.EQ
                                                           e21
                                                           FStar_Pervasives_Native.None
                                                           "branch body"
                                                          in
                                                       (match uu____24118
                                                        with
                                                        | (prob,wl3) ->
                                                            ((let uu____24139
                                                                =
                                                                FStar_All.pipe_left
                                                                  (FStar_TypeChecker_Env.debug
                                                                    wl3.tcenv)
                                                                  (FStar_Options.Other
                                                                    "Rel")
                                                                 in
                                                              if uu____24139
                                                              then
                                                                let uu____24144
                                                                  =
                                                                  prob_to_string
                                                                    env prob
                                                                   in
                                                                let uu____24146
                                                                  =
                                                                  FStar_Syntax_Print.binders_to_string
                                                                    ", "
                                                                    scope
                                                                   in
                                                                FStar_Util.print2
                                                                  "Created problem for branches %s with scope %s\n"
                                                                  uu____24144
                                                                  uu____24146
                                                              else ());
                                                             (let uu____24152
                                                                =
                                                                solve_branches
                                                                  wl3 rs1 rs2
                                                                 in
                                                              FStar_Util.bind_opt
                                                                uu____24152
                                                                (fun
                                                                   uu____24188
                                                                    ->
                                                                   match uu____24188
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
                    | uu____24317 -> FStar_Pervasives_Native.None  in
                  let uu____24358 = solve_branches wl brs1 brs2  in
                  (match uu____24358 with
                   | FStar_Pervasives_Native.None  ->
                       if wl.smt_ok
                       then by_smt ()
                       else
                         (let uu____24384 =
                            FStar_Thunk.mkv "Tm_match branches don't match"
                             in
                          giveup env uu____24384 orig)
                   | FStar_Pervasives_Native.Some (sub_probs,wl1) ->
                       let uu____24411 =
                         mk_t_problem wl1 [] orig s1
                           FStar_TypeChecker_Common.EQ s2
                           FStar_Pervasives_Native.None "match scrutinee"
                          in
                       (match uu____24411 with
                        | (sc_prob,wl2) ->
                            let sub_probs1 = ([], sc_prob) :: sub_probs  in
                            let formula =
                              let uu____24445 =
                                FStar_List.map
                                  (fun uu____24457  ->
                                     match uu____24457 with
                                     | (scope,p) ->
                                         FStar_TypeChecker_Env.close_forall
                                           wl2.tcenv scope (p_guard p))
                                  sub_probs1
                                 in
                              FStar_Syntax_Util.mk_conj_l uu____24445  in
                            let tx =
                              FStar_Syntax_Unionfind.new_transaction ()  in
                            let wl3 =
                              solve_prob orig
                                (FStar_Pervasives_Native.Some formula) [] wl2
                               in
                            let uu____24466 =
                              let uu____24467 =
                                let uu____24468 =
                                  FStar_List.map FStar_Pervasives_Native.snd
                                    sub_probs1
                                   in
                                attempt uu____24468
                                  (let uu___3437_24476 = wl3  in
                                   {
                                     attempting =
                                       (uu___3437_24476.attempting);
                                     wl_deferred =
                                       (uu___3437_24476.wl_deferred);
                                     wl_deferred_to_tac =
                                       (uu___3437_24476.wl_deferred_to_tac);
                                     ctr = (uu___3437_24476.ctr);
                                     defer_ok = (uu___3437_24476.defer_ok);
                                     smt_ok = false;
                                     umax_heuristic_ok =
                                       (uu___3437_24476.umax_heuristic_ok);
                                     tcenv = (uu___3437_24476.tcenv);
                                     wl_implicits =
                                       (uu___3437_24476.wl_implicits)
                                   })
                                 in
                              solve env uu____24467  in
                            (match uu____24466 with
                             | Success (ds,ds',imp) ->
                                 (FStar_Syntax_Unionfind.commit tx;
                                  Success (ds, ds', imp))
                             | Failed uu____24482 ->
                                 (FStar_Syntax_Unionfind.rollback tx;
                                  if wl3.smt_ok
                                  then by_smt ()
                                  else
                                    (let uu____24491 =
                                       FStar_Thunk.mkv
                                         "Could not unify matches without SMT"
                                        in
                                     giveup env uu____24491 orig)))))
              | (FStar_Syntax_Syntax.Tm_match uu____24494,uu____24495) ->
                  let head1 =
                    let uu____24519 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24519
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24565 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24565
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24611 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24611
                    then
                      let uu____24615 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24617 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24619 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24615 uu____24617 uu____24619
                    else ());
                   (let no_free_uvars t =
                      (let uu____24633 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24633) &&
                        (let uu____24637 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24637)
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
                      let uu____24656 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24656 = FStar_Syntax_Util.Equal  in
                    let uu____24657 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24657
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24661 = equal t1 t2  in
                         (if uu____24661
                          then
                            let uu____24664 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24664
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24669 =
                            let uu____24676 = equal t1 t2  in
                            if uu____24676
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24689 = mk_eq2 wl env orig t1 t2  in
                               match uu____24689 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24669 with
                          | (guard,wl1) ->
                              let uu____24710 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24710))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_uinst uu____24713,uu____24714) ->
                  let head1 =
                    let uu____24722 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24722
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24768 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24768
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____24814 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____24814
                    then
                      let uu____24818 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____24820 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____24822 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____24818 uu____24820 uu____24822
                    else ());
                   (let no_free_uvars t =
                      (let uu____24836 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____24836) &&
                        (let uu____24840 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____24840)
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
                      let uu____24859 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____24859 = FStar_Syntax_Util.Equal  in
                    let uu____24860 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____24860
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____24864 = equal t1 t2  in
                         (if uu____24864
                          then
                            let uu____24867 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____24867
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____24872 =
                            let uu____24879 = equal t1 t2  in
                            if uu____24879
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____24892 = mk_eq2 wl env orig t1 t2  in
                               match uu____24892 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____24872 with
                          | (guard,wl1) ->
                              let uu____24913 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____24913))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_name uu____24916,uu____24917) ->
                  let head1 =
                    let uu____24919 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____24919
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____24965 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____24965
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25011 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25011
                    then
                      let uu____25015 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25017 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25019 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25015 uu____25017 uu____25019
                    else ());
                   (let no_free_uvars t =
                      (let uu____25033 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25033) &&
                        (let uu____25037 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25037)
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
                      let uu____25056 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25056 = FStar_Syntax_Util.Equal  in
                    let uu____25057 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25057
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25061 = equal t1 t2  in
                         (if uu____25061
                          then
                            let uu____25064 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25064
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25069 =
                            let uu____25076 = equal t1 t2  in
                            if uu____25076
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25089 = mk_eq2 wl env orig t1 t2  in
                               match uu____25089 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25069 with
                          | (guard,wl1) ->
                              let uu____25110 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25110))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_constant uu____25113,uu____25114) ->
                  let head1 =
                    let uu____25116 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25116
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25162 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25162
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25208 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25208
                    then
                      let uu____25212 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25214 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25216 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25212 uu____25214 uu____25216
                    else ());
                   (let no_free_uvars t =
                      (let uu____25230 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25230) &&
                        (let uu____25234 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25234)
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
                      let uu____25253 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25253 = FStar_Syntax_Util.Equal  in
                    let uu____25254 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25254
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25258 = equal t1 t2  in
                         (if uu____25258
                          then
                            let uu____25261 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25261
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25266 =
                            let uu____25273 = equal t1 t2  in
                            if uu____25273
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25286 = mk_eq2 wl env orig t1 t2  in
                               match uu____25286 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25266 with
                          | (guard,wl1) ->
                              let uu____25307 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25307))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_fvar uu____25310,uu____25311) ->
                  let head1 =
                    let uu____25313 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25313
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25353 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25353
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25393 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25393
                    then
                      let uu____25397 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25399 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25401 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25397 uu____25399 uu____25401
                    else ());
                   (let no_free_uvars t =
                      (let uu____25415 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25415) &&
                        (let uu____25419 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25419)
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
                      let uu____25438 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25438 = FStar_Syntax_Util.Equal  in
                    let uu____25439 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25439
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25443 = equal t1 t2  in
                         (if uu____25443
                          then
                            let uu____25446 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25446
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25451 =
                            let uu____25458 = equal t1 t2  in
                            if uu____25458
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25471 = mk_eq2 wl env orig t1 t2  in
                               match uu____25471 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25451 with
                          | (guard,wl1) ->
                              let uu____25492 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25492))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_app uu____25495,uu____25496) ->
                  let head1 =
                    let uu____25514 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25514
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25554 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25554
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25594 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25594
                    then
                      let uu____25598 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25600 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25602 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25598 uu____25600 uu____25602
                    else ());
                   (let no_free_uvars t =
                      (let uu____25616 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25616) &&
                        (let uu____25620 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25620)
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
                      let uu____25639 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25639 = FStar_Syntax_Util.Equal  in
                    let uu____25640 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25640
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25644 = equal t1 t2  in
                         (if uu____25644
                          then
                            let uu____25647 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25647
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25652 =
                            let uu____25659 = equal t1 t2  in
                            if uu____25659
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25672 = mk_eq2 wl env orig t1 t2  in
                               match uu____25672 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25652 with
                          | (guard,wl1) ->
                              let uu____25693 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25693))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25696,FStar_Syntax_Syntax.Tm_match uu____25697) ->
                  let head1 =
                    let uu____25721 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25721
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25761 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25761
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25801 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25801
                    then
                      let uu____25805 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25807 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____25809 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25805 uu____25807 uu____25809
                    else ());
                   (let no_free_uvars t =
                      (let uu____25823 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____25823) &&
                        (let uu____25827 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____25827)
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
                      let uu____25846 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____25846 = FStar_Syntax_Util.Equal  in
                    let uu____25847 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____25847
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____25851 = equal t1 t2  in
                         (if uu____25851
                          then
                            let uu____25854 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____25854
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____25859 =
                            let uu____25866 = equal t1 t2  in
                            if uu____25866
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____25879 = mk_eq2 wl env orig t1 t2  in
                               match uu____25879 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____25859 with
                          | (guard,wl1) ->
                              let uu____25900 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____25900))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____25903,FStar_Syntax_Syntax.Tm_uinst uu____25904) ->
                  let head1 =
                    let uu____25912 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____25912
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____25952 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____25952
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____25992 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____25992
                    then
                      let uu____25996 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____25998 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26000 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____25996 uu____25998 uu____26000
                    else ());
                   (let no_free_uvars t =
                      (let uu____26014 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26014) &&
                        (let uu____26018 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26018)
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
                      let uu____26037 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26037 = FStar_Syntax_Util.Equal  in
                    let uu____26038 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26038
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26042 = equal t1 t2  in
                         (if uu____26042
                          then
                            let uu____26045 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26045
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26050 =
                            let uu____26057 = equal t1 t2  in
                            if uu____26057
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26070 = mk_eq2 wl env orig t1 t2  in
                               match uu____26070 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26050 with
                          | (guard,wl1) ->
                              let uu____26091 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26091))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26094,FStar_Syntax_Syntax.Tm_name uu____26095) ->
                  let head1 =
                    let uu____26097 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26097
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26137 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26137
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26177 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26177
                    then
                      let uu____26181 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26183 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26185 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26181 uu____26183 uu____26185
                    else ());
                   (let no_free_uvars t =
                      (let uu____26199 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26199) &&
                        (let uu____26203 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26203)
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
                      let uu____26222 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26222 = FStar_Syntax_Util.Equal  in
                    let uu____26223 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26223
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26227 = equal t1 t2  in
                         (if uu____26227
                          then
                            let uu____26230 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26230
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26235 =
                            let uu____26242 = equal t1 t2  in
                            if uu____26242
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26255 = mk_eq2 wl env orig t1 t2  in
                               match uu____26255 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26235 with
                          | (guard,wl1) ->
                              let uu____26276 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26276))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26279,FStar_Syntax_Syntax.Tm_constant uu____26280) ->
                  let head1 =
                    let uu____26282 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26282
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26322 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26322
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26362 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26362
                    then
                      let uu____26366 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26368 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26370 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26366 uu____26368 uu____26370
                    else ());
                   (let no_free_uvars t =
                      (let uu____26384 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26384) &&
                        (let uu____26388 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26388)
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
                      let uu____26407 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26407 = FStar_Syntax_Util.Equal  in
                    let uu____26408 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26408
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26412 = equal t1 t2  in
                         (if uu____26412
                          then
                            let uu____26415 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26415
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26420 =
                            let uu____26427 = equal t1 t2  in
                            if uu____26427
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26440 = mk_eq2 wl env orig t1 t2  in
                               match uu____26440 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26420 with
                          | (guard,wl1) ->
                              let uu____26461 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26461))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26464,FStar_Syntax_Syntax.Tm_fvar uu____26465) ->
                  let head1 =
                    let uu____26467 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26467
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26513 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26513
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26559 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26559
                    then
                      let uu____26563 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26565 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26567 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26563 uu____26565 uu____26567
                    else ());
                   (let no_free_uvars t =
                      (let uu____26581 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26581) &&
                        (let uu____26585 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26585)
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
                      let uu____26604 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26604 = FStar_Syntax_Util.Equal  in
                    let uu____26605 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26605
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26609 = equal t1 t2  in
                         (if uu____26609
                          then
                            let uu____26612 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26612
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26617 =
                            let uu____26624 = equal t1 t2  in
                            if uu____26624
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26637 = mk_eq2 wl env orig t1 t2  in
                               match uu____26637 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26617 with
                          | (guard,wl1) ->
                              let uu____26658 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26658))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (uu____26661,FStar_Syntax_Syntax.Tm_app uu____26662) ->
                  let head1 =
                    let uu____26680 = FStar_Syntax_Util.head_and_args t1  in
                    FStar_All.pipe_right uu____26680
                      FStar_Pervasives_Native.fst
                     in
                  let head2 =
                    let uu____26720 = FStar_Syntax_Util.head_and_args t2  in
                    FStar_All.pipe_right uu____26720
                      FStar_Pervasives_Native.fst
                     in
                  ((let uu____26760 =
                      FStar_TypeChecker_Env.debug env
                        (FStar_Options.Other "Rel")
                       in
                    if uu____26760
                    then
                      let uu____26764 =
                        FStar_Util.string_of_int
                          problem.FStar_TypeChecker_Common.pid
                         in
                      let uu____26766 =
                        FStar_Syntax_Print.term_to_string head1  in
                      let uu____26768 =
                        FStar_Syntax_Print.term_to_string head2  in
                      FStar_Util.print3
                        ">> (%s)\n>>> head1 = %s\n>>> head2 = %s\n"
                        uu____26764 uu____26766 uu____26768
                    else ());
                   (let no_free_uvars t =
                      (let uu____26782 = FStar_Syntax_Free.uvars t  in
                       FStar_Util.set_is_empty uu____26782) &&
                        (let uu____26786 = FStar_Syntax_Free.univs t  in
                         FStar_Util.set_is_empty uu____26786)
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
                      let uu____26805 = FStar_Syntax_Util.eq_tm t12 t22  in
                      uu____26805 = FStar_Syntax_Util.Equal  in
                    let uu____26806 =
                      ((((FStar_TypeChecker_Env.is_interpreted env head1) ||
                           (FStar_TypeChecker_Env.is_interpreted env head2))
                          &&
                          (problem.FStar_TypeChecker_Common.relation =
                             FStar_TypeChecker_Common.EQ))
                         && (no_free_uvars t1))
                        && (no_free_uvars t2)
                       in
                    if uu____26806
                    then
                      (if Prims.op_Negation wl.smt_ok
                       then
                         let uu____26810 = equal t1 t2  in
                         (if uu____26810
                          then
                            let uu____26813 =
                              solve_prob orig FStar_Pervasives_Native.None []
                                wl
                               in
                            solve env uu____26813
                          else
                            rigid_rigid_delta env problem wl head1 head2 t1
                              t2)
                       else
                         (let uu____26818 =
                            let uu____26825 = equal t1 t2  in
                            if uu____26825
                            then (FStar_Pervasives_Native.None, wl)
                            else
                              (let uu____26838 = mk_eq2 wl env orig t1 t2  in
                               match uu____26838 with
                               | (g,wl1) ->
                                   ((FStar_Pervasives_Native.Some g), wl1))
                             in
                          match uu____26818 with
                          | (guard,wl1) ->
                              let uu____26859 = solve_prob orig guard [] wl1
                                 in
                              solve env uu____26859))
                    else rigid_rigid_delta env problem wl head1 head2 t1 t2))
              | (FStar_Syntax_Syntax.Tm_let
                 uu____26862,FStar_Syntax_Syntax.Tm_let uu____26863) ->
                  let uu____26890 = FStar_Syntax_Util.term_eq t1 t2  in
                  if uu____26890
                  then
                    let uu____26893 =
                      solve_prob orig FStar_Pervasives_Native.None [] wl  in
                    solve env uu____26893
                  else
                    (let uu____26896 = FStar_Thunk.mkv "Tm_let mismatch"  in
                     giveup env uu____26896 orig)
              | (FStar_Syntax_Syntax.Tm_let uu____26899,uu____26900) ->
                  let uu____26914 =
                    let uu____26920 =
                      let uu____26922 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26924 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26926 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26928 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26922 uu____26924 uu____26926 uu____26928
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26920)
                     in
                  FStar_Errors.raise_error uu____26914
                    t1.FStar_Syntax_Syntax.pos
              | (uu____26932,FStar_Syntax_Syntax.Tm_let uu____26933) ->
                  let uu____26947 =
                    let uu____26953 =
                      let uu____26955 = FStar_Syntax_Print.tag_of_term t1  in
                      let uu____26957 = FStar_Syntax_Print.tag_of_term t2  in
                      let uu____26959 = FStar_Syntax_Print.term_to_string t1
                         in
                      let uu____26961 = FStar_Syntax_Print.term_to_string t2
                         in
                      FStar_Util.format4
                        "Internal error: unexpected flex-flex of %s and %s\n>>> (%s) -- (%s)"
                        uu____26955 uu____26957 uu____26959 uu____26961
                       in
                    (FStar_Errors.Fatal_UnificationNotWellFormed,
                      uu____26953)
                     in
                  FStar_Errors.raise_error uu____26947
                    t1.FStar_Syntax_Syntax.pos
              | uu____26965 ->
                  let uu____26970 = FStar_Thunk.mkv "head tag mismatch"  in
                  giveup env uu____26970 orig))))

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
          (let uu____27036 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "EQ")
              in
           if uu____27036
           then
             let uu____27041 =
               let uu____27043 = FStar_Syntax_Syntax.mk_Comp c1_comp  in
               FStar_Syntax_Print.comp_to_string uu____27043  in
             let uu____27044 =
               let uu____27046 = FStar_Syntax_Syntax.mk_Comp c2_comp  in
               FStar_Syntax_Print.comp_to_string uu____27046  in
             FStar_Util.print2
               "solve_c is using an equality constraint (%s vs %s)\n"
               uu____27041 uu____27044
           else ());
          (let uu____27050 =
             let uu____27052 =
               FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name
                 c2_comp.FStar_Syntax_Syntax.effect_name
                in
             Prims.op_Negation uu____27052  in
           if uu____27050
           then
             let uu____27055 =
               FStar_Thunk.mk
                 (fun uu____27060  ->
                    let uu____27061 =
                      FStar_Syntax_Print.lid_to_string
                        c1_comp.FStar_Syntax_Syntax.effect_name
                       in
                    let uu____27063 =
                      FStar_Syntax_Print.lid_to_string
                        c2_comp.FStar_Syntax_Syntax.effect_name
                       in
                    FStar_Util.format2 "incompatible effects: %s <> %s"
                      uu____27061 uu____27063)
                in
             giveup env uu____27055 orig
           else
             if
               (FStar_List.length c1_comp.FStar_Syntax_Syntax.effect_args) <>
                 (FStar_List.length c2_comp.FStar_Syntax_Syntax.effect_args)
             then
               (let uu____27085 =
                  FStar_Thunk.mk
                    (fun uu____27090  ->
                       let uu____27091 =
                         FStar_Syntax_Print.args_to_string
                           c1_comp.FStar_Syntax_Syntax.effect_args
                          in
                       let uu____27093 =
                         FStar_Syntax_Print.args_to_string
                           c2_comp.FStar_Syntax_Syntax.effect_args
                          in
                       FStar_Util.format2
                         "incompatible effect arguments: %s <> %s"
                         uu____27091 uu____27093)
                   in
                giveup env uu____27085 orig)
             else
               (let uu____27098 =
                  FStar_List.fold_left2
                    (fun uu____27119  ->
                       fun u1  ->
                         fun u2  ->
                           match uu____27119 with
                           | (univ_sub_probs,wl1) ->
                               let uu____27140 =
                                 let uu____27145 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u1)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 let uu____27146 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_type u2)
                                     FStar_Pervasives_Native.None
                                     FStar_Range.dummyRange
                                    in
                                 sub_prob wl1 uu____27145
                                   FStar_TypeChecker_Common.EQ uu____27146
                                   "effect universes"
                                  in
                               (match uu____27140 with
                                | (p,wl2) ->
                                    ((FStar_List.append univ_sub_probs [p]),
                                      wl2))) ([], wl)
                    c1_comp.FStar_Syntax_Syntax.comp_univs
                    c2_comp.FStar_Syntax_Syntax.comp_univs
                   in
                match uu____27098 with
                | (univ_sub_probs,wl1) ->
                    let uu____27166 =
                      sub_prob wl1 c1_comp.FStar_Syntax_Syntax.result_typ
                        FStar_TypeChecker_Common.EQ
                        c2_comp.FStar_Syntax_Syntax.result_typ
                        "effect ret type"
                       in
                    (match uu____27166 with
                     | (ret_sub_prob,wl2) ->
                         let uu____27174 =
                           FStar_List.fold_right2
                             (fun uu____27211  ->
                                fun uu____27212  ->
                                  fun uu____27213  ->
                                    match (uu____27211, uu____27212,
                                            uu____27213)
                                    with
                                    | ((a1,uu____27257),(a2,uu____27259),
                                       (arg_sub_probs,wl3)) ->
                                        let uu____27292 =
                                          sub_prob wl3 a1
                                            FStar_TypeChecker_Common.EQ a2
                                            "effect arg"
                                           in
                                        (match uu____27292 with
                                         | (p,wl4) ->
                                             ((p :: arg_sub_probs), wl4)))
                             c1_comp.FStar_Syntax_Syntax.effect_args
                             c2_comp.FStar_Syntax_Syntax.effect_args
                             ([], wl2)
                            in
                         (match uu____27174 with
                          | (arg_sub_probs,wl3) ->
                              let sub_probs =
                                let uu____27319 =
                                  let uu____27322 =
                                    let uu____27325 =
                                      FStar_All.pipe_right
                                        g_lift.FStar_TypeChecker_Common.deferred
                                        (FStar_List.map
                                           FStar_Pervasives_Native.snd)
                                       in
                                    FStar_List.append arg_sub_probs
                                      uu____27325
                                     in
                                  FStar_List.append [ret_sub_prob]
                                    uu____27322
                                   in
                                FStar_List.append univ_sub_probs uu____27319
                                 in
                              let guard =
                                let guard =
                                  let uu____27347 =
                                    FStar_List.map p_guard sub_probs  in
                                  FStar_Syntax_Util.mk_conj_l uu____27347  in
                                match g_lift.FStar_TypeChecker_Common.guard_f
                                with
                                | FStar_TypeChecker_Common.Trivial  -> guard
                                | FStar_TypeChecker_Common.NonTrivial f ->
                                    FStar_Syntax_Util.mk_conj guard f
                                 in
                              let wl4 =
                                let uu___3590_27356 = wl3  in
                                {
                                  attempting = (uu___3590_27356.attempting);
                                  wl_deferred = (uu___3590_27356.wl_deferred);
                                  wl_deferred_to_tac =
                                    (uu___3590_27356.wl_deferred_to_tac);
                                  ctr = (uu___3590_27356.ctr);
                                  defer_ok = (uu___3590_27356.defer_ok);
                                  smt_ok = (uu___3590_27356.smt_ok);
                                  umax_heuristic_ok =
                                    (uu___3590_27356.umax_heuristic_ok);
                                  tcenv = (uu___3590_27356.tcenv);
                                  wl_implicits =
                                    (FStar_List.append
                                       g_lift.FStar_TypeChecker_Common.implicits
                                       wl3.wl_implicits)
                                }  in
                              let wl5 =
                                solve_prob orig
                                  (FStar_Pervasives_Native.Some guard) [] wl4
                                 in
                              let uu____27358 = attempt sub_probs wl5  in
                              solve env uu____27358))))
           in
        let solve_layered_sub c11 edge c21 =
          (let uu____27376 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffects")
              in
           if uu____27376
           then
             let uu____27381 =
               let uu____27383 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27383
                 FStar_Syntax_Print.comp_to_string
                in
             let uu____27385 =
               let uu____27387 =
                 FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27387
                 FStar_Syntax_Print.comp_to_string
                in
             FStar_Util.print2 "solve_layered_sub c1: %s and c2: %s\n"
               uu____27381 uu____27385
           else ());
          (let uu____27392 =
             let uu____27397 =
               let uu____27402 =
                 FStar_All.pipe_right c11 FStar_Syntax_Syntax.mk_Comp  in
               FStar_All.pipe_right uu____27402
                 ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                    env)
                in
             FStar_All.pipe_right uu____27397
               (fun uu____27419  ->
                  match uu____27419 with
                  | (c,g) ->
                      let uu____27430 = FStar_Syntax_Util.comp_to_comp_typ c
                         in
                      (uu____27430, g))
              in
           match uu____27392 with
           | (c12,g_lift) ->
               ((let uu____27434 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "LayeredEffects")
                    in
                 if uu____27434
                 then
                   let uu____27439 =
                     let uu____27441 =
                       FStar_All.pipe_right c12 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27441
                       FStar_Syntax_Print.comp_to_string
                      in
                   let uu____27443 =
                     let uu____27445 =
                       FStar_All.pipe_right c21 FStar_Syntax_Syntax.mk_Comp
                        in
                     FStar_All.pipe_right uu____27445
                       FStar_Syntax_Print.comp_to_string
                      in
                   FStar_Util.print2
                     "solve_layered_sub after lift c1: %s and c2: %s\n"
                     uu____27439 uu____27443
                 else ());
                if
                  problem.FStar_TypeChecker_Common.relation =
                    FStar_TypeChecker_Common.EQ
                then solve_eq c12 c21 g_lift
                else
                  (let r = FStar_TypeChecker_Env.get_range env  in
                   let wl1 =
                     let uu___3610_27455 = wl  in
                     {
                       attempting = (uu___3610_27455.attempting);
                       wl_deferred = (uu___3610_27455.wl_deferred);
                       wl_deferred_to_tac =
                         (uu___3610_27455.wl_deferred_to_tac);
                       ctr = (uu___3610_27455.ctr);
                       defer_ok = (uu___3610_27455.defer_ok);
                       smt_ok = (uu___3610_27455.smt_ok);
                       umax_heuristic_ok =
                         (uu___3610_27455.umax_heuristic_ok);
                       tcenv = (uu___3610_27455.tcenv);
                       wl_implicits =
                         (FStar_List.append
                            g_lift.FStar_TypeChecker_Common.implicits
                            wl.wl_implicits)
                     }  in
                   let uu____27456 =
                     let rec is_uvar1 t =
                       let uu____27470 =
                         let uu____27471 = FStar_Syntax_Subst.compress t  in
                         uu____27471.FStar_Syntax_Syntax.n  in
                       match uu____27470 with
                       | FStar_Syntax_Syntax.Tm_uvar uu____27475 -> true
                       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____27490) ->
                           is_uvar1 t1
                       | FStar_Syntax_Syntax.Tm_app (t1,uu____27496) ->
                           is_uvar1 t1
                       | uu____27521 -> false  in
                     FStar_List.fold_right2
                       (fun uu____27555  ->
                          fun uu____27556  ->
                            fun uu____27557  ->
                              match (uu____27555, uu____27556, uu____27557)
                              with
                              | ((a1,uu____27601),(a2,uu____27603),(is_sub_probs,wl2))
                                  ->
                                  let uu____27636 = is_uvar1 a1  in
                                  if uu____27636
                                  then
                                    ((let uu____27646 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other
                                             "LayeredEffects")
                                         in
                                      if uu____27646
                                      then
                                        let uu____27651 =
                                          FStar_Syntax_Print.term_to_string
                                            a1
                                           in
                                        let uu____27653 =
                                          FStar_Syntax_Print.term_to_string
                                            a2
                                           in
                                        FStar_Util.print2
                                          "solve_layered_sub: adding index equality for %s and %s (since a1 uvar)\n"
                                          uu____27651 uu____27653
                                      else ());
                                     (let uu____27658 =
                                        sub_prob wl2 a1
                                          FStar_TypeChecker_Common.EQ a2
                                          "l.h.s. effect index uvar"
                                         in
                                      match uu____27658 with
                                      | (p,wl3) -> ((p :: is_sub_probs), wl3)))
                                  else (is_sub_probs, wl2))
                       c12.FStar_Syntax_Syntax.effect_args
                       c21.FStar_Syntax_Syntax.effect_args ([], wl1)
                      in
                   match uu____27456 with
                   | (is_sub_probs,wl2) ->
                       let uu____27686 =
                         sub_prob wl2 c12.FStar_Syntax_Syntax.result_typ
                           problem.FStar_TypeChecker_Common.relation
                           c21.FStar_Syntax_Syntax.result_typ "result type"
                          in
                       (match uu____27686 with
                        | (ret_sub_prob,wl3) ->
                            let uu____27694 =
                              let uu____27699 =
                                let uu____27700 =
                                  FStar_All.pipe_right
                                    c21.FStar_Syntax_Syntax.effect_name
                                    (FStar_TypeChecker_Env.get_effect_decl
                                       env)
                                   in
                                FStar_All.pipe_right uu____27700
                                  FStar_Syntax_Util.get_stronger_vc_combinator
                                 in
                              FStar_All.pipe_right uu____27699
                                (fun ts  ->
                                   FStar_TypeChecker_Env.inst_tscheme_with ts
                                     c21.FStar_Syntax_Syntax.comp_univs)
                               in
                            (match uu____27694 with
                             | (uu____27707,stronger_t) ->
                                 let stronger_t_shape_error s =
                                   let uu____27718 =
                                     FStar_Ident.string_of_lid
                                       c21.FStar_Syntax_Syntax.effect_name
                                      in
                                   let uu____27720 =
                                     FStar_Syntax_Print.term_to_string
                                       stronger_t
                                      in
                                   FStar_Util.format3
                                     "Unexpected shape of stronger for %s, reason: %s (t:%s)"
                                     uu____27718 s uu____27720
                                    in
                                 let uu____27723 =
                                   let uu____27752 =
                                     let uu____27753 =
                                       FStar_Syntax_Subst.compress stronger_t
                                        in
                                     uu____27753.FStar_Syntax_Syntax.n  in
                                   match uu____27752 with
                                   | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____27813 =
                                         FStar_Syntax_Subst.open_comp bs c
                                          in
                                       (match uu____27813 with
                                        | (a::bs1,c3) ->
                                            let uu____27869 =
                                              let uu____27888 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one))
                                                 in
                                              FStar_All.pipe_right
                                                uu____27888
                                                (fun uu____27992  ->
                                                   match uu____27992 with
                                                   | (l1,l2) ->
                                                       let uu____28065 =
                                                         FStar_List.hd l2  in
                                                       (l1, uu____28065))
                                               in
                                            (match uu____27869 with
                                             | (rest_bs,f_b) ->
                                                 (a, rest_bs, f_b, c3)))
                                   | uu____28170 ->
                                       let uu____28171 =
                                         let uu____28177 =
                                           stronger_t_shape_error
                                             "not an arrow or not enough binders"
                                            in
                                         (FStar_Errors.Fatal_UnexpectedExpressionType,
                                           uu____28177)
                                          in
                                       FStar_Errors.raise_error uu____28171 r
                                    in
                                 (match uu____27723 with
                                  | (a_b,rest_bs,f_b,stronger_c) ->
                                      let uu____28253 =
                                        let uu____28260 =
                                          let uu____28261 =
                                            let uu____28262 =
                                              let uu____28269 =
                                                FStar_All.pipe_right a_b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              (uu____28269,
                                                (c21.FStar_Syntax_Syntax.result_typ))
                                               in
                                            FStar_Syntax_Syntax.NT
                                              uu____28262
                                             in
                                          [uu____28261]  in
                                        FStar_TypeChecker_Env.uvars_for_binders
                                          env rest_bs uu____28260
                                          (fun b  ->
                                             let uu____28285 =
                                               FStar_Syntax_Print.binder_to_string
                                                 b
                                                in
                                             let uu____28287 =
                                               FStar_Ident.string_of_lid
                                                 c21.FStar_Syntax_Syntax.effect_name
                                                in
                                             let uu____28289 =
                                               FStar_Range.string_of_range r
                                                in
                                             FStar_Util.format3
                                               "implicit for binder %s in stronger of %s at %s"
                                               uu____28285 uu____28287
                                               uu____28289) r
                                         in
                                      (match uu____28253 with
                                       | (rest_bs_uvars,g_uvars) ->
                                           ((let uu____28299 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____28299
                                             then
                                               let uu____28304 =
                                                 FStar_List.fold_left
                                                   (fun s  ->
                                                      fun u  ->
                                                        let uu____28313 =
                                                          let uu____28315 =
                                                            FStar_Syntax_Print.term_to_string
                                                              u
                                                             in
                                                          Prims.op_Hat ";;;;"
                                                            uu____28315
                                                           in
                                                        Prims.op_Hat s
                                                          uu____28313) ""
                                                   rest_bs_uvars
                                                  in
                                               FStar_Util.print1
                                                 "Introduced uvars for subcomp: %s\n"
                                                 uu____28304
                                             else ());
                                            (let wl4 =
                                               let uu___3682_28323 = wl3  in
                                               {
                                                 attempting =
                                                   (uu___3682_28323.attempting);
                                                 wl_deferred =
                                                   (uu___3682_28323.wl_deferred);
                                                 wl_deferred_to_tac =
                                                   (uu___3682_28323.wl_deferred_to_tac);
                                                 ctr = (uu___3682_28323.ctr);
                                                 defer_ok =
                                                   (uu___3682_28323.defer_ok);
                                                 smt_ok =
                                                   (uu___3682_28323.smt_ok);
                                                 umax_heuristic_ok =
                                                   (uu___3682_28323.umax_heuristic_ok);
                                                 tcenv =
                                                   (uu___3682_28323.tcenv);
                                                 wl_implicits =
                                                   (FStar_List.append
                                                      g_uvars.FStar_TypeChecker_Common.implicits
                                                      wl3.wl_implicits)
                                               }  in
                                             let substs =
                                               FStar_List.map2
                                                 (fun b  ->
                                                    fun t  ->
                                                      let uu____28348 =
                                                        let uu____28355 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        (uu____28355, t)  in
                                                      FStar_Syntax_Syntax.NT
                                                        uu____28348) (a_b ::
                                                 rest_bs)
                                                 ((c21.FStar_Syntax_Syntax.result_typ)
                                                 :: rest_bs_uvars)
                                                in
                                             let uu____28372 =
                                               let f_sort_is =
                                                 let uu____28382 =
                                                   let uu____28383 =
                                                     let uu____28386 =
                                                       let uu____28387 =
                                                         FStar_All.pipe_right
                                                           f_b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       uu____28387.FStar_Syntax_Syntax.sort
                                                        in
                                                     FStar_Syntax_Subst.compress
                                                       uu____28386
                                                      in
                                                   uu____28383.FStar_Syntax_Syntax.n
                                                    in
                                                 match uu____28382 with
                                                 | FStar_Syntax_Syntax.Tm_app
                                                     (uu____28398,uu____28399::is)
                                                     ->
                                                     let uu____28441 =
                                                       FStar_All.pipe_right
                                                         is
                                                         (FStar_List.map
                                                            FStar_Pervasives_Native.fst)
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____28441
                                                       (FStar_List.map
                                                          (FStar_Syntax_Subst.subst
                                                             substs))
                                                 | uu____28474 ->
                                                     let uu____28475 =
                                                       let uu____28481 =
                                                         stronger_t_shape_error
                                                           "type of f is not a repr type"
                                                          in
                                                       (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                         uu____28481)
                                                        in
                                                     FStar_Errors.raise_error
                                                       uu____28475 r
                                                  in
                                               let uu____28487 =
                                                 FStar_All.pipe_right
                                                   c12.FStar_Syntax_Syntax.effect_args
                                                   (FStar_List.map
                                                      FStar_Pervasives_Native.fst)
                                                  in
                                               FStar_List.fold_left2
                                                 (fun uu____28522  ->
                                                    fun f_sort_i  ->
                                                      fun c1_i  ->
                                                        match uu____28522
                                                        with
                                                        | (ps,wl5) ->
                                                            let uu____28543 =
                                                              sub_prob wl5
                                                                f_sort_i
                                                                FStar_TypeChecker_Common.EQ
                                                                c1_i
                                                                "indices of c1"
                                                               in
                                                            (match uu____28543
                                                             with
                                                             | (p,wl6) ->
                                                                 ((FStar_List.append
                                                                    ps 
                                                                    [p]),
                                                                   wl6)))
                                                 ([], wl4) f_sort_is
                                                 uu____28487
                                                in
                                             match uu____28372 with
                                             | (f_sub_probs,wl5) ->
                                                 let stronger_ct =
                                                   let uu____28568 =
                                                     FStar_All.pipe_right
                                                       stronger_c
                                                       (FStar_Syntax_Subst.subst_comp
                                                          substs)
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____28568
                                                     FStar_Syntax_Util.comp_to_comp_typ
                                                    in
                                                 let uu____28569 =
                                                   let g_sort_is =
                                                     let uu____28579 =
                                                       let uu____28580 =
                                                         FStar_Syntax_Subst.compress
                                                           stronger_ct.FStar_Syntax_Syntax.result_typ
                                                          in
                                                       uu____28580.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____28579 with
                                                     | FStar_Syntax_Syntax.Tm_app
                                                         (uu____28585,uu____28586::is)
                                                         ->
                                                         FStar_All.pipe_right
                                                           is
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.fst)
                                                     | uu____28646 ->
                                                         let uu____28647 =
                                                           let uu____28653 =
                                                             stronger_t_shape_error
                                                               "return type is not a repr type"
                                                              in
                                                           (FStar_Errors.Fatal_UnexpectedExpressionType,
                                                             uu____28653)
                                                            in
                                                         FStar_Errors.raise_error
                                                           uu____28647 r
                                                      in
                                                   let uu____28659 =
                                                     FStar_All.pipe_right
                                                       c21.FStar_Syntax_Syntax.effect_args
                                                       (FStar_List.map
                                                          FStar_Pervasives_Native.fst)
                                                      in
                                                   FStar_List.fold_left2
                                                     (fun uu____28694  ->
                                                        fun g_sort_i  ->
                                                          fun c2_i  ->
                                                            match uu____28694
                                                            with
                                                            | (ps,wl6) ->
                                                                let uu____28715
                                                                  =
                                                                  sub_prob
                                                                    wl6
                                                                    g_sort_i
                                                                    FStar_TypeChecker_Common.EQ
                                                                    c2_i
                                                                    "indices of c2"
                                                                   in
                                                                (match uu____28715
                                                                 with
                                                                 | (p,wl7) ->
                                                                    ((FStar_List.append
                                                                    ps [p]),
                                                                    wl7)))
                                                     ([], wl5) g_sort_is
                                                     uu____28659
                                                    in
                                                 (match uu____28569 with
                                                  | (g_sub_probs,wl6) ->
                                                      let fml =
                                                        let uu____28742 =
                                                          let uu____28747 =
                                                            FStar_List.hd
                                                              stronger_ct.FStar_Syntax_Syntax.comp_univs
                                                             in
                                                          let uu____28748 =
                                                            let uu____28749 =
                                                              FStar_List.hd
                                                                stronger_ct.FStar_Syntax_Syntax.effect_args
                                                               in
                                                            FStar_Pervasives_Native.fst
                                                              uu____28749
                                                             in
                                                          (uu____28747,
                                                            uu____28748)
                                                           in
                                                        match uu____28742
                                                        with
                                                        | (u,wp) ->
                                                            FStar_TypeChecker_Env.pure_precondition_for_trivial_post
                                                              env u
                                                              stronger_ct.FStar_Syntax_Syntax.result_typ
                                                              wp
                                                              FStar_Range.dummyRange
                                                         in
                                                      let sub_probs =
                                                        let uu____28777 =
                                                          let uu____28780 =
                                                            let uu____28783 =
                                                              let uu____28786
                                                                =
                                                                FStar_All.pipe_right
                                                                  g_lift.FStar_TypeChecker_Common.deferred
                                                                  (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                 in
                                                              FStar_List.append
                                                                g_sub_probs
                                                                uu____28786
                                                               in
                                                            FStar_List.append
                                                              f_sub_probs
                                                              uu____28783
                                                             in
                                                          FStar_List.append
                                                            is_sub_probs
                                                            uu____28780
                                                           in
                                                        ret_sub_prob ::
                                                          uu____28777
                                                         in
                                                      let guard =
                                                        let guard =
                                                          let uu____28810 =
                                                            FStar_List.map
                                                              p_guard
                                                              sub_probs
                                                             in
                                                          FStar_Syntax_Util.mk_conj_l
                                                            uu____28810
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
                                                        let uu____28821 =
                                                          let uu____28824 =
                                                            FStar_Syntax_Util.mk_conj
                                                              guard fml
                                                             in
                                                          FStar_All.pipe_left
                                                            (fun _28827  ->
                                                               FStar_Pervasives_Native.Some
                                                                 _28827)
                                                            uu____28824
                                                           in
                                                        solve_prob orig
                                                          uu____28821 [] wl6
                                                         in
                                                      let uu____28828 =
                                                        attempt sub_probs wl7
                                                         in
                                                      solve env uu____28828))))))))))
           in
        let solve_sub c11 edge c21 =
          let r = FStar_TypeChecker_Env.get_range env  in
          let lift_c1 uu____28851 =
            let univs1 =
              match c11.FStar_Syntax_Syntax.comp_univs with
              | [] ->
                  let uu____28853 =
                    env.FStar_TypeChecker_Env.universe_of env
                      c11.FStar_Syntax_Syntax.result_typ
                     in
                  [uu____28853]
              | x -> x  in
            let c12 =
              let uu___3748_28856 = c11  in
              {
                FStar_Syntax_Syntax.comp_univs = univs1;
                FStar_Syntax_Syntax.effect_name =
                  (uu___3748_28856.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___3748_28856.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___3748_28856.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags =
                  (uu___3748_28856.FStar_Syntax_Syntax.flags)
              }  in
            let uu____28857 =
              let uu____28862 =
                FStar_All.pipe_right
                  (let uu___3751_28864 = c12  in
                   {
                     FStar_Syntax_Syntax.comp_univs = univs1;
                     FStar_Syntax_Syntax.effect_name =
                       (uu___3751_28864.FStar_Syntax_Syntax.effect_name);
                     FStar_Syntax_Syntax.result_typ =
                       (uu___3751_28864.FStar_Syntax_Syntax.result_typ);
                     FStar_Syntax_Syntax.effect_args =
                       (uu___3751_28864.FStar_Syntax_Syntax.effect_args);
                     FStar_Syntax_Syntax.flags =
                       (uu___3751_28864.FStar_Syntax_Syntax.flags)
                   }) FStar_Syntax_Syntax.mk_Comp
                 in
              FStar_All.pipe_right uu____28862
                ((edge.FStar_TypeChecker_Env.mlift).FStar_TypeChecker_Env.mlift_wp
                   env)
               in
            FStar_All.pipe_right uu____28857
              (fun uu____28878  ->
                 match uu____28878 with
                 | (c,g) ->
                     let uu____28885 =
                       let uu____28887 = FStar_TypeChecker_Env.is_trivial g
                          in
                       Prims.op_Negation uu____28887  in
                     if uu____28885
                     then
                       let uu____28890 =
                         let uu____28896 =
                           let uu____28898 =
                             FStar_Ident.string_of_lid
                               c12.FStar_Syntax_Syntax.effect_name
                              in
                           let uu____28900 =
                             FStar_Ident.string_of_lid
                               c21.FStar_Syntax_Syntax.effect_name
                              in
                           FStar_Util.format2
                             "Lift between wp-effects (%s~>%s) should not have returned a non-trivial guard"
                             uu____28898 uu____28900
                            in
                         (FStar_Errors.Fatal_UnexpectedEffect, uu____28896)
                          in
                       FStar_Errors.raise_error uu____28890 r
                     else FStar_Syntax_Util.comp_to_comp_typ c)
             in
          let uu____28906 =
            FStar_TypeChecker_Env.is_layered_effect env
              c21.FStar_Syntax_Syntax.effect_name
             in
          if uu____28906
          then solve_layered_sub c11 edge c21
          else
            if
              problem.FStar_TypeChecker_Common.relation =
                FStar_TypeChecker_Common.EQ
            then
              (let uu____28912 = lift_c1 ()  in
               solve_eq uu____28912 c21 FStar_TypeChecker_Env.trivial_guard)
            else
              (let is_null_wp_2 =
                 FStar_All.pipe_right c21.FStar_Syntax_Syntax.flags
                   (FStar_Util.for_some
                      (fun uu___31_28921  ->
                         match uu___31_28921 with
                         | FStar_Syntax_Syntax.TOTAL  -> true
                         | FStar_Syntax_Syntax.MLEFFECT  -> true
                         | FStar_Syntax_Syntax.SOMETRIVIAL  -> true
                         | uu____28926 -> false))
                  in
               let uu____28928 =
                 match ((c11.FStar_Syntax_Syntax.effect_args),
                         (c21.FStar_Syntax_Syntax.effect_args))
                 with
                 | ((wp1,uu____28958)::uu____28959,(wp2,uu____28961)::uu____28962)
                     -> (wp1, wp2)
                 | uu____29035 ->
                     let uu____29060 =
                       let uu____29066 =
                         let uu____29068 =
                           FStar_Syntax_Print.lid_to_string
                             c11.FStar_Syntax_Syntax.effect_name
                            in
                         let uu____29070 =
                           FStar_Syntax_Print.lid_to_string
                             c21.FStar_Syntax_Syntax.effect_name
                            in
                         FStar_Util.format2
                           "Got effects %s and %s, expected normalized effects"
                           uu____29068 uu____29070
                          in
                       (FStar_Errors.Fatal_ExpectNormalizedEffect,
                         uu____29066)
                        in
                     FStar_Errors.raise_error uu____29060
                       env.FStar_TypeChecker_Env.range
                  in
               match uu____28928 with
               | (wpc1,wpc2) ->
                   let uu____29080 = FStar_Util.physical_equality wpc1 wpc2
                      in
                   if uu____29080
                   then
                     let uu____29083 =
                       problem_using_guard orig
                         c11.FStar_Syntax_Syntax.result_typ
                         problem.FStar_TypeChecker_Common.relation
                         c21.FStar_Syntax_Syntax.result_typ
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29083 wl
                   else
                     (let uu____29087 =
                        let uu____29094 =
                          FStar_TypeChecker_Env.effect_decl_opt env
                            c21.FStar_Syntax_Syntax.effect_name
                           in
                        FStar_Util.must uu____29094  in
                      match uu____29087 with
                      | (c2_decl,qualifiers) ->
                          let uu____29115 =
                            FStar_All.pipe_right qualifiers
                              (FStar_List.contains
                                 FStar_Syntax_Syntax.Reifiable)
                             in
                          if uu____29115
                          then
                            let c1_repr =
                              let uu____29122 =
                                let uu____29123 =
                                  let uu____29124 = lift_c1 ()  in
                                  FStar_Syntax_Syntax.mk_Comp uu____29124  in
                                let uu____29125 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c11.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29123 uu____29125
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.4"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29122
                               in
                            let c2_repr =
                              let uu____29128 =
                                let uu____29129 =
                                  FStar_Syntax_Syntax.mk_Comp c21  in
                                let uu____29130 =
                                  env.FStar_TypeChecker_Env.universe_of env
                                    c21.FStar_Syntax_Syntax.result_typ
                                   in
                                FStar_TypeChecker_Env.reify_comp env
                                  uu____29129 uu____29130
                                 in
                              norm_with_steps
                                "FStar.TypeChecker.Rel.norm_with_steps.5"
                                [FStar_TypeChecker_Env.UnfoldUntil
                                   FStar_Syntax_Syntax.delta_constant;
                                FStar_TypeChecker_Env.Weak;
                                FStar_TypeChecker_Env.HNF] env uu____29128
                               in
                            let uu____29132 =
                              let uu____29137 =
                                let uu____29139 =
                                  FStar_Syntax_Print.term_to_string c1_repr
                                   in
                                let uu____29141 =
                                  FStar_Syntax_Print.term_to_string c2_repr
                                   in
                                FStar_Util.format2
                                  "sub effect repr: %s <: %s" uu____29139
                                  uu____29141
                                 in
                              sub_prob wl c1_repr
                                problem.FStar_TypeChecker_Common.relation
                                c2_repr uu____29137
                               in
                            (match uu____29132 with
                             | (prob,wl1) ->
                                 let wl2 =
                                   solve_prob orig
                                     (FStar_Pervasives_Native.Some
                                        (p_guard prob)) [] wl1
                                    in
                                 let uu____29147 = attempt [prob] wl2  in
                                 solve env uu____29147)
                          else
                            (let g =
                               if env.FStar_TypeChecker_Env.lax
                               then FStar_Syntax_Util.t_true
                               else
                                 (let wpc1_2 =
                                    let uu____29167 = lift_c1 ()  in
                                    FStar_All.pipe_right uu____29167
                                      (fun ct  ->
                                         FStar_List.hd
                                           ct.FStar_Syntax_Syntax.effect_args)
                                     in
                                  if is_null_wp_2
                                  then
                                    ((let uu____29190 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "Rel")
                                         in
                                      if uu____29190
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
                                        let uu____29200 =
                                          FStar_All.pipe_right c2_decl
                                            FStar_Syntax_Util.get_wp_trivial_combinator
                                           in
                                        match uu____29200 with
                                        | FStar_Pervasives_Native.None  ->
                                            failwith
                                              "Rel doesn't yet handle undefined trivial combinator in an effect"
                                        | FStar_Pervasives_Native.Some t -> t
                                         in
                                      let uu____29207 =
                                        let uu____29214 =
                                          let uu____29215 =
                                            let uu____29232 =
                                              FStar_TypeChecker_Env.inst_effect_fun_with
                                                [c1_univ] env c2_decl trivial
                                               in
                                            let uu____29235 =
                                              let uu____29246 =
                                                FStar_Syntax_Syntax.as_arg
                                                  c11.FStar_Syntax_Syntax.result_typ
                                                 in
                                              [uu____29246; wpc1_2]  in
                                            (uu____29232, uu____29235)  in
                                          FStar_Syntax_Syntax.Tm_app
                                            uu____29215
                                           in
                                        FStar_Syntax_Syntax.mk uu____29214
                                         in
                                      uu____29207
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
                                     let uu____29295 =
                                       let uu____29302 =
                                         let uu____29303 =
                                           let uu____29320 =
                                             FStar_TypeChecker_Env.inst_effect_fun_with
                                               [c2_univ] env c2_decl stronger
                                              in
                                           let uu____29323 =
                                             let uu____29334 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c21.FStar_Syntax_Syntax.result_typ
                                                in
                                             let uu____29343 =
                                               let uu____29354 =
                                                 FStar_Syntax_Syntax.as_arg
                                                   wpc2
                                                  in
                                               [uu____29354; wpc1_2]  in
                                             uu____29334 :: uu____29343  in
                                           (uu____29320, uu____29323)  in
                                         FStar_Syntax_Syntax.Tm_app
                                           uu____29303
                                          in
                                       FStar_Syntax_Syntax.mk uu____29302  in
                                     uu____29295 FStar_Pervasives_Native.None
                                       r))
                                in
                             (let uu____29408 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "Rel")
                                 in
                              if uu____29408
                              then
                                let uu____29413 =
                                  let uu____29415 =
                                    FStar_TypeChecker_Normalize.normalize
                                      [FStar_TypeChecker_Env.Iota;
                                      FStar_TypeChecker_Env.Eager_unfolding;
                                      FStar_TypeChecker_Env.Primops;
                                      FStar_TypeChecker_Env.Simplify] env g
                                     in
                                  FStar_Syntax_Print.term_to_string
                                    uu____29415
                                   in
                                FStar_Util.print1
                                  "WP guard (simplifed) is (%s)\n"
                                  uu____29413
                              else ());
                             (let uu____29419 =
                                sub_prob wl
                                  c11.FStar_Syntax_Syntax.result_typ
                                  problem.FStar_TypeChecker_Common.relation
                                  c21.FStar_Syntax_Syntax.result_typ
                                  "result type"
                                 in
                              match uu____29419 with
                              | (base_prob,wl1) ->
                                  let wl2 =
                                    let uu____29428 =
                                      let uu____29431 =
                                        FStar_Syntax_Util.mk_conj
                                          (p_guard base_prob) g
                                         in
                                      FStar_All.pipe_left
                                        (fun _29434  ->
                                           FStar_Pervasives_Native.Some
                                             _29434) uu____29431
                                       in
                                    solve_prob orig uu____29428 [] wl1  in
                                  let uu____29435 = attempt [base_prob] wl2
                                     in
                                  solve env uu____29435))))
           in
        let uu____29436 = FStar_Util.physical_equality c1 c2  in
        if uu____29436
        then
          let uu____29439 =
            solve_prob orig FStar_Pervasives_Native.None [] wl  in
          solve env uu____29439
        else
          ((let uu____29443 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Rel")
               in
            if uu____29443
            then
              let uu____29448 = FStar_Syntax_Print.comp_to_string c1  in
              let uu____29450 = FStar_Syntax_Print.comp_to_string c2  in
              FStar_Util.print3 "solve_c %s %s %s\n" uu____29448
                (rel_to_string problem.FStar_TypeChecker_Common.relation)
                uu____29450
            else ());
           (let uu____29455 =
              let uu____29464 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c1  in
              let uu____29467 =
                FStar_TypeChecker_Normalize.ghost_to_pure env c2  in
              (uu____29464, uu____29467)  in
            match uu____29455 with
            | (c11,c21) ->
                (match ((c11.FStar_Syntax_Syntax.n),
                         (c21.FStar_Syntax_Syntax.n))
                 with
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29485),FStar_Syntax_Syntax.Total
                    (t2,uu____29487)) when
                     FStar_TypeChecker_Env.non_informative env t2 ->
                     let uu____29504 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29504 wl
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29506,FStar_Syntax_Syntax.Total uu____29507) ->
                     let uu____29524 =
                       FStar_Thunk.mkv
                         "incompatible monad ordering: GTot </: Tot"
                        in
                     giveup env uu____29524 orig
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29528),FStar_Syntax_Syntax.Total
                    (t2,uu____29530)) ->
                     let uu____29547 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29547 wl
                 | (FStar_Syntax_Syntax.GTotal
                    (t1,uu____29550),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29552)) ->
                     let uu____29569 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29569 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29572),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29574)) when
                     problem.FStar_TypeChecker_Common.relation =
                       FStar_TypeChecker_Common.SUB
                     ->
                     let uu____29591 =
                       problem_using_guard orig t1
                         problem.FStar_TypeChecker_Common.relation t2
                         FStar_Pervasives_Native.None "result type"
                        in
                     solve_t env uu____29591 wl
                 | (FStar_Syntax_Syntax.Total
                    (t1,uu____29594),FStar_Syntax_Syntax.GTotal
                    (t2,uu____29596)) ->
                     let uu____29613 = FStar_Thunk.mkv "GTot =/= Tot"  in
                     giveup env uu____29613 orig
                 | (FStar_Syntax_Syntax.GTotal
                    uu____29616,FStar_Syntax_Syntax.Comp uu____29617) ->
                     let uu____29626 =
                       let uu___3875_29629 = problem  in
                       let uu____29632 =
                         let uu____29633 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29633
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3875_29629.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29632;
                         FStar_TypeChecker_Common.relation =
                           (uu___3875_29629.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3875_29629.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3875_29629.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3875_29629.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3875_29629.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3875_29629.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3875_29629.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3875_29629.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29626 wl
                 | (FStar_Syntax_Syntax.Total
                    uu____29634,FStar_Syntax_Syntax.Comp uu____29635) ->
                     let uu____29644 =
                       let uu___3875_29647 = problem  in
                       let uu____29650 =
                         let uu____29651 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29651
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3875_29647.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs = uu____29650;
                         FStar_TypeChecker_Common.relation =
                           (uu___3875_29647.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs =
                           (uu___3875_29647.FStar_TypeChecker_Common.rhs);
                         FStar_TypeChecker_Common.element =
                           (uu___3875_29647.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3875_29647.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3875_29647.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3875_29647.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3875_29647.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3875_29647.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29644 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29652,FStar_Syntax_Syntax.GTotal uu____29653) ->
                     let uu____29662 =
                       let uu___3887_29665 = problem  in
                       let uu____29668 =
                         let uu____29669 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29669
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3887_29665.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3887_29665.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3887_29665.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29668;
                         FStar_TypeChecker_Common.element =
                           (uu___3887_29665.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3887_29665.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3887_29665.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3887_29665.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3887_29665.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3887_29665.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29662 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29670,FStar_Syntax_Syntax.Total uu____29671) ->
                     let uu____29680 =
                       let uu___3887_29683 = problem  in
                       let uu____29686 =
                         let uu____29687 =
                           FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                         FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp
                           uu____29687
                          in
                       {
                         FStar_TypeChecker_Common.pid =
                           (uu___3887_29683.FStar_TypeChecker_Common.pid);
                         FStar_TypeChecker_Common.lhs =
                           (uu___3887_29683.FStar_TypeChecker_Common.lhs);
                         FStar_TypeChecker_Common.relation =
                           (uu___3887_29683.FStar_TypeChecker_Common.relation);
                         FStar_TypeChecker_Common.rhs = uu____29686;
                         FStar_TypeChecker_Common.element =
                           (uu___3887_29683.FStar_TypeChecker_Common.element);
                         FStar_TypeChecker_Common.logical_guard =
                           (uu___3887_29683.FStar_TypeChecker_Common.logical_guard);
                         FStar_TypeChecker_Common.logical_guard_uvar =
                           (uu___3887_29683.FStar_TypeChecker_Common.logical_guard_uvar);
                         FStar_TypeChecker_Common.reason =
                           (uu___3887_29683.FStar_TypeChecker_Common.reason);
                         FStar_TypeChecker_Common.loc =
                           (uu___3887_29683.FStar_TypeChecker_Common.loc);
                         FStar_TypeChecker_Common.rank =
                           (uu___3887_29683.FStar_TypeChecker_Common.rank)
                       }  in
                     solve_c env uu____29680 wl
                 | (FStar_Syntax_Syntax.Comp
                    uu____29688,FStar_Syntax_Syntax.Comp uu____29689) ->
                     let uu____29690 =
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
                     if uu____29690
                     then
                       let uu____29693 =
                         problem_using_guard orig
                           (FStar_Syntax_Util.comp_result c11)
                           problem.FStar_TypeChecker_Common.relation
                           (FStar_Syntax_Util.comp_result c21)
                           FStar_Pervasives_Native.None "result type"
                          in
                       solve_t env uu____29693 wl
                     else
                       (let c1_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c11  in
                        let c2_comp =
                          FStar_TypeChecker_Env.comp_to_comp_typ env c21  in
                        if
                          problem.FStar_TypeChecker_Common.relation =
                            FStar_TypeChecker_Common.EQ
                        then
                          let uu____29700 =
                            let uu____29705 =
                              FStar_Ident.lid_equals
                                c1_comp.FStar_Syntax_Syntax.effect_name
                                c2_comp.FStar_Syntax_Syntax.effect_name
                               in
                            if uu____29705
                            then (c1_comp, c2_comp)
                            else
                              (let uu____29714 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c11
                                  in
                               let uu____29715 =
                                 FStar_TypeChecker_Env.unfold_effect_abbrev
                                   env c21
                                  in
                               (uu____29714, uu____29715))
                             in
                          match uu____29700 with
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
                           (let uu____29723 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Rel")
                               in
                            if uu____29723
                            then
                              FStar_Util.print2 "solve_c for %s and %s\n"
                                (c12.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                                (c22.FStar_Syntax_Syntax.effect_name).FStar_Ident.str
                            else ());
                           (let uu____29731 =
                              FStar_TypeChecker_Env.monad_leq env
                                c12.FStar_Syntax_Syntax.effect_name
                                c22.FStar_Syntax_Syntax.effect_name
                               in
                            match uu____29731 with
                            | FStar_Pervasives_Native.None  ->
                                let uu____29734 =
                                  FStar_Thunk.mk
                                    (fun uu____29739  ->
                                       let uu____29740 =
                                         FStar_Syntax_Print.lid_to_string
                                           c12.FStar_Syntax_Syntax.effect_name
                                          in
                                       let uu____29742 =
                                         FStar_Syntax_Print.lid_to_string
                                           c22.FStar_Syntax_Syntax.effect_name
                                          in
                                       FStar_Util.format2
                                         "incompatible monad ordering: %s </: %s"
                                         uu____29740 uu____29742)
                                   in
                                giveup env uu____29734 orig
                            | FStar_Pervasives_Native.Some edge ->
                                solve_sub c12 edge c22))))))

let (print_pending_implicits :
  FStar_TypeChecker_Common.guard_t -> Prims.string) =
  fun g  ->
    let uu____29753 =
      FStar_All.pipe_right g.FStar_TypeChecker_Common.implicits
        (FStar_List.map
           (fun i  ->
              FStar_Syntax_Print.term_to_string
                i.FStar_TypeChecker_Common.imp_tm))
       in
    FStar_All.pipe_right uu____29753 (FStar_String.concat ", ")
  
let (ineqs_to_string :
  (FStar_Syntax_Syntax.universe Prims.list * (FStar_Syntax_Syntax.universe *
    FStar_Syntax_Syntax.universe) Prims.list) -> Prims.string)
  =
  fun ineqs  ->
    let vars =
      let uu____29803 =
        FStar_All.pipe_right (FStar_Pervasives_Native.fst ineqs)
          (FStar_List.map FStar_Syntax_Print.univ_to_string)
         in
      FStar_All.pipe_right uu____29803 (FStar_String.concat ", ")  in
    let ineqs1 =
      let uu____29828 =
        FStar_All.pipe_right (FStar_Pervasives_Native.snd ineqs)
          (FStar_List.map
             (fun uu____29859  ->
                match uu____29859 with
                | (u1,u2) ->
                    let uu____29867 = FStar_Syntax_Print.univ_to_string u1
                       in
                    let uu____29869 = FStar_Syntax_Print.univ_to_string u2
                       in
                    FStar_Util.format2 "%s < %s" uu____29867 uu____29869))
         in
      FStar_All.pipe_right uu____29828 (FStar_String.concat ", ")  in
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
      | (FStar_TypeChecker_Common.Trivial ,[],(uu____29906,[])) when
          let uu____29933 = FStar_Options.print_implicits ()  in
          Prims.op_Negation uu____29933 -> "{}"
      | uu____29936 ->
          let form =
            match g.FStar_TypeChecker_Common.guard_f with
            | FStar_TypeChecker_Common.Trivial  -> "trivial"
            | FStar_TypeChecker_Common.NonTrivial f ->
                let uu____29963 =
                  ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                      (FStar_Options.Other "Rel"))
                     ||
                     (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                        FStar_Options.Extreme))
                    || (FStar_Options.print_implicits ())
                   in
                if uu____29963
                then FStar_TypeChecker_Normalize.term_to_string env f
                else "non-trivial"
             in
          let carry defs =
            let uu____29994 =
              FStar_List.map
                (fun uu____30008  ->
                   match uu____30008 with
                   | (msg,x) ->
                       let uu____30019 =
                         let uu____30021 = prob_to_string env x  in
                         Prims.op_Hat ": " uu____30021  in
                       Prims.op_Hat msg uu____30019) defs
               in
            FStar_All.pipe_right uu____29994 (FStar_String.concat ",\n")  in
          let imps = print_pending_implicits g  in
          let uu____30031 = carry g.FStar_TypeChecker_Common.deferred  in
          let uu____30033 = carry g.FStar_TypeChecker_Common.deferred_to_tac
             in
          let uu____30035 =
            ineqs_to_string g.FStar_TypeChecker_Common.univ_ineqs  in
          FStar_Util.format5
            "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t deferred_to_tac={\n%s};\n\t univ_ineqs={%s};\n\t implicits={%s}}\n"
            form uu____30031 uu____30033 uu____30035 imps
  
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
                  let uu____30092 =
                    (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                       (FStar_Options.Other "ExplainRel"))
                      ||
                      (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "Rel"))
                     in
                  if uu____30092
                  then
                    let uu____30100 =
                      FStar_TypeChecker_Normalize.term_to_string env lhs  in
                    let uu____30102 =
                      FStar_TypeChecker_Normalize.term_to_string env rhs  in
                    FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" uu____30100
                      (rel_to_string rel) uu____30102
                  else "TOP"  in
                let uu____30108 =
                  new_problem wl env lhs rel rhs elt loc reason  in
                match uu____30108 with
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
              let uu____30168 =
                let uu____30171 = FStar_TypeChecker_Env.get_range env  in
                FStar_All.pipe_left
                  (fun _30174  -> FStar_Pervasives_Native.Some _30174)
                  uu____30171
                 in
              FStar_Syntax_Syntax.new_bv uu____30168 t1  in
            let uu____30175 =
              let uu____30180 = FStar_TypeChecker_Env.get_range env  in
              new_t_problem wl env t1 rel t2 (FStar_Pervasives_Native.Some x)
                uu____30180
               in
            match uu____30175 with | (p,wl1) -> (p, x, wl1)
  
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
        (let uu____30252 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "RelBench")
            in
         if uu____30252
         then
           let uu____30257 =
             FStar_Common.string_of_list
               (fun p  -> FStar_Util.string_of_int (p_pid p))
               probs.attempting
              in
           FStar_Util.print1 "solving problems %s {\n" uu____30257
         else ());
        (let uu____30264 =
           FStar_Util.record_time (fun uu____30271  -> solve env probs)  in
         match uu____30264 with
         | (sol,ms) ->
             ((let uu____30285 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "RelBench")
                  in
               if uu____30285
               then
                 let uu____30290 = FStar_Util.string_of_int ms  in
                 FStar_Util.print1 "} solved in %s ms\n" uu____30290
               else ());
              (match sol with
               | Success (deferred,defer_to_tac,implicits) ->
                   let uu____30306 =
                     FStar_Util.record_time
                       (fun uu____30313  -> FStar_Syntax_Unionfind.commit tx)
                      in
                   (match uu____30306 with
                    | ((),ms1) ->
                        ((let uu____30326 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "RelBench")
                             in
                          if uu____30326
                          then
                            let uu____30331 = FStar_Util.string_of_int ms1
                               in
                            FStar_Util.print1 "committed in %s ms\n"
                              uu____30331
                          else ());
                         FStar_Pervasives_Native.Some
                           (deferred, defer_to_tac, implicits)))
               | Failed (d,s) ->
                   ((let uu____30345 =
                       (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                          (FStar_Options.Other "ExplainRel"))
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env)
                            (FStar_Options.Other "Rel"))
                        in
                     if uu____30345
                     then
                       let uu____30352 = explain env d s  in
                       FStar_All.pipe_left FStar_Util.print_string
                         uu____30352
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
          ((let uu____30380 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                (FStar_Options.Other "Simplification")
               in
            if uu____30380
            then
              let uu____30385 = FStar_Syntax_Print.term_to_string f  in
              FStar_Util.print1 "Simplifying guard %s\n" uu____30385
            else ());
           (let f1 =
              norm_with_steps "FStar.TypeChecker.Rel.norm_with_steps.6"
                [FStar_TypeChecker_Env.Beta;
                FStar_TypeChecker_Env.Eager_unfolding;
                FStar_TypeChecker_Env.Simplify;
                FStar_TypeChecker_Env.Primops;
                FStar_TypeChecker_Env.NoFullNorm] env f
               in
            (let uu____30393 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "Simplification")
                in
             if uu____30393
             then
               let uu____30398 = FStar_Syntax_Print.term_to_string f1  in
               FStar_Util.print1 "Simplified guard to %s\n" uu____30398
             else ());
            (let f2 =
               let uu____30404 =
                 let uu____30405 = FStar_Syntax_Util.unmeta f1  in
                 uu____30405.FStar_Syntax_Syntax.n  in
               match uu____30404 with
               | FStar_Syntax_Syntax.Tm_fvar fv when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.true_lid
                   -> FStar_TypeChecker_Common.Trivial
               | uu____30409 -> FStar_TypeChecker_Common.NonTrivial f1  in
             let uu___4006_30410 = g  in
             {
               FStar_TypeChecker_Common.guard_f = f2;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4006_30410.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4006_30410.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4006_30410.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4006_30410.FStar_TypeChecker_Common.implicits)
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
            let uu____30462 =
              let uu____30463 =
                let uu____30464 =
                  FStar_All.pipe_right (p_guard prob)
                    (fun _30465  ->
                       FStar_TypeChecker_Common.NonTrivial _30465)
                   in
                {
                  FStar_TypeChecker_Common.guard_f = uu____30464;
                  FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                  FStar_TypeChecker_Common.deferred = deferred;
                  FStar_TypeChecker_Common.univ_ineqs = ([], []);
                  FStar_TypeChecker_Common.implicits = implicits
                }  in
              simplify_guard env uu____30463  in
            FStar_All.pipe_left
              (fun _30472  -> FStar_Pervasives_Native.Some _30472)
              uu____30462
  
let with_guard_no_simp :
  'Auu____30482 .
    'Auu____30482 ->
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
            let uu____30531 =
              let uu____30532 =
                FStar_All.pipe_right (p_guard prob)
                  (fun _30533  -> FStar_TypeChecker_Common.NonTrivial _30533)
                 in
              {
                FStar_TypeChecker_Common.guard_f = uu____30532;
                FStar_TypeChecker_Common.deferred_to_tac = defer_to_tac;
                FStar_TypeChecker_Common.deferred = deferred;
                FStar_TypeChecker_Common.univ_ineqs = ([], []);
                FStar_TypeChecker_Common.implicits = implicits
              }  in
            FStar_Pervasives_Native.Some uu____30531
  
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
          (let uu____30566 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "Rel")
              in
           if uu____30566
           then
             let uu____30571 = FStar_Syntax_Print.term_to_string t1  in
             let uu____30573 = FStar_Syntax_Print.term_to_string t2  in
             FStar_Util.print2 "try_teq of %s and %s {\n" uu____30571
               uu____30573
           else ());
          (let uu____30578 =
             let uu____30583 = FStar_TypeChecker_Env.get_range env  in
             new_t_problem (empty_worklist env) env t1
               FStar_TypeChecker_Common.EQ t2 FStar_Pervasives_Native.None
               uu____30583
              in
           match uu____30578 with
           | (prob,wl) ->
               let g =
                 let uu____30591 =
                   solve_and_commit env (singleton wl prob smt_ok)
                     (fun uu____30601  -> FStar_Pervasives_Native.None)
                    in
                 FStar_All.pipe_left (with_guard env prob) uu____30591  in
               ((let uu____30623 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                     (FStar_Options.Other "Rel")
                    in
                 if uu____30623
                 then
                   let uu____30628 =
                     FStar_Common.string_of_option (guard_to_string env) g
                      in
                   FStar_Util.print1 "} res = %s\n" uu____30628
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
        let uu____30649 = try_teq true env t1 t2  in
        match uu____30649 with
        | FStar_Pervasives_Native.None  ->
            ((let uu____30654 = FStar_TypeChecker_Env.get_range env  in
              let uu____30655 =
                FStar_TypeChecker_Err.basic_type_error env
                  FStar_Pervasives_Native.None t2 t1
                 in
              FStar_Errors.log_issue uu____30654 uu____30655);
             FStar_TypeChecker_Common.trivial_guard)
        | FStar_Pervasives_Native.Some g ->
            ((let uu____30663 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                  (FStar_Options.Other "Rel")
                 in
              if uu____30663
              then
                let uu____30668 = FStar_Syntax_Print.term_to_string t1  in
                let uu____30670 = FStar_Syntax_Print.term_to_string t2  in
                let uu____30672 = guard_to_string env g  in
                FStar_Util.print3
                  "teq of %s and %s succeeded with guard %s\n" uu____30668
                  uu____30670 uu____30672
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
        (let uu____30696 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30696
         then
           let uu____30701 = FStar_Syntax_Print.term_to_string t1  in
           let uu____30703 = FStar_Syntax_Print.term_to_string t2  in
           FStar_Util.print2 "get_teq_predicate of %s and %s {\n" uu____30701
             uu____30703
         else ());
        (let uu____30708 =
           new_t_prob (empty_worklist env) env t1 FStar_TypeChecker_Common.EQ
             t2
            in
         match uu____30708 with
         | (prob,x,wl) ->
             let g =
               let uu____30723 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____30734  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____30723  in
             ((let uu____30756 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Rel")
                  in
               if uu____30756
               then
                 let uu____30761 =
                   FStar_Common.string_of_option (guard_to_string env) g  in
                 FStar_Util.print1 "} res teq predicate = %s\n" uu____30761
               else ());
              (match g with
               | FStar_Pervasives_Native.None  ->
                   FStar_Pervasives_Native.None
               | FStar_Pervasives_Native.Some g1 ->
                   let uu____30769 =
                     let uu____30770 = FStar_Syntax_Syntax.mk_binder x  in
                     FStar_TypeChecker_Env.abstract_guard uu____30770 g1  in
                   FStar_Pervasives_Native.Some uu____30769)))
  
let (subtype_fail :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun e  ->
      fun t1  ->
        fun t2  ->
          let uu____30792 = FStar_TypeChecker_Env.get_range env  in
          let uu____30793 =
            FStar_TypeChecker_Err.basic_type_error env
              (FStar_Pervasives_Native.Some e) t2 t1
             in
          FStar_Errors.log_issue uu____30792 uu____30793
  
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
        (let uu____30822 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____30822
         then
           let uu____30827 = FStar_Syntax_Print.comp_to_string c1  in
           let uu____30829 = FStar_Syntax_Print.comp_to_string c2  in
           FStar_Util.print3 "sub_comp of %s --and-- %s --with-- %s\n"
             uu____30827 uu____30829
             (if rel = FStar_TypeChecker_Common.EQ then "EQ" else "SUB")
         else ());
        (let uu____30840 =
           let uu____30847 = FStar_TypeChecker_Env.get_range env  in
           new_problem (empty_worklist env) env c1 rel c2
             FStar_Pervasives_Native.None uu____30847 "sub_comp"
            in
         match uu____30840 with
         | (prob,wl) ->
             let prob1 = FStar_TypeChecker_Common.CProb prob  in
             (def_check_prob "sub_comp" prob1;
              (let uu____30860 =
                 FStar_Util.record_time
                   (fun uu____30872  ->
                      let uu____30873 =
                        solve_and_commit env (singleton wl prob1 true)
                          (fun uu____30884  -> FStar_Pervasives_Native.None)
                         in
                      FStar_All.pipe_left (with_guard env prob1) uu____30873)
                  in
               match uu____30860 with
               | (r,ms) ->
                   ((let uu____30916 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                         (FStar_Options.Other "RelBench")
                        in
                     if uu____30916
                     then
                       let uu____30921 = FStar_Syntax_Print.comp_to_string c1
                          in
                       let uu____30923 = FStar_Syntax_Print.comp_to_string c2
                          in
                       let uu____30925 = FStar_Util.string_of_int ms  in
                       FStar_Util.print4
                         "sub_comp of %s --and-- %s --with-- %s --- solved in %s ms\n"
                         uu____30921 uu____30923
                         (if rel = FStar_TypeChecker_Common.EQ
                          then "EQ"
                          else "SUB") uu____30925
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
      fun uu____30963  ->
        match uu____30963 with
        | (variables,ineqs) ->
            let fail1 u1 u2 =
              FStar_Syntax_Unionfind.rollback tx;
              (let uu____31006 =
                 let uu____31012 =
                   let uu____31014 = FStar_Syntax_Print.univ_to_string u1  in
                   let uu____31016 = FStar_Syntax_Print.univ_to_string u2  in
                   FStar_Util.format2 "Universe %s and %s are incompatible"
                     uu____31014 uu____31016
                    in
                 (FStar_Errors.Fatal_IncompatibleUniverse, uu____31012)  in
               let uu____31020 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____31006 uu____31020)
               in
            let equiv1 v1 v' =
              let uu____31033 =
                let uu____31038 = FStar_Syntax_Subst.compress_univ v1  in
                let uu____31039 = FStar_Syntax_Subst.compress_univ v'  in
                (uu____31038, uu____31039)  in
              match uu____31033 with
              | (FStar_Syntax_Syntax.U_unif v0,FStar_Syntax_Syntax.U_unif
                 v0') -> FStar_Syntax_Unionfind.univ_equiv v0 v0'
              | uu____31059 -> false  in
            let sols =
              FStar_All.pipe_right variables
                (FStar_List.collect
                   (fun v1  ->
                      let uu____31090 = FStar_Syntax_Subst.compress_univ v1
                         in
                      match uu____31090 with
                      | FStar_Syntax_Syntax.U_unif uu____31097 ->
                          let lower_bounds_of_v =
                            FStar_All.pipe_right ineqs
                              (FStar_List.collect
                                 (fun uu____31126  ->
                                    match uu____31126 with
                                    | (u,v') ->
                                        let uu____31135 = equiv1 v1 v'  in
                                        if uu____31135
                                        then
                                          let uu____31140 =
                                            FStar_All.pipe_right variables
                                              (FStar_Util.for_some (equiv1 u))
                                             in
                                          (if uu____31140 then [] else [u])
                                        else []))
                             in
                          let lb =
                            FStar_TypeChecker_Normalize.normalize_universe
                              env
                              (FStar_Syntax_Syntax.U_max lower_bounds_of_v)
                             in
                          [(lb, v1)]
                      | uu____31161 -> []))
               in
            let uu____31166 =
              let wl =
                let uu___4119_31170 = empty_worklist env  in
                {
                  attempting = (uu___4119_31170.attempting);
                  wl_deferred = (uu___4119_31170.wl_deferred);
                  wl_deferred_to_tac = (uu___4119_31170.wl_deferred_to_tac);
                  ctr = (uu___4119_31170.ctr);
                  defer_ok = false;
                  smt_ok = (uu___4119_31170.smt_ok);
                  umax_heuristic_ok = (uu___4119_31170.umax_heuristic_ok);
                  tcenv = (uu___4119_31170.tcenv);
                  wl_implicits = (uu___4119_31170.wl_implicits)
                }  in
              FStar_All.pipe_right sols
                (FStar_List.map
                   (fun uu____31189  ->
                      match uu____31189 with
                      | (lb,v1) ->
                          let uu____31196 =
                            solve_universe_eq (~- Prims.int_one) wl lb v1  in
                          (match uu____31196 with
                           | USolved wl1 -> ()
                           | uu____31199 -> fail1 lb v1)))
               in
            let rec check_ineq uu____31210 =
              match uu____31210 with
              | (u,v1) ->
                  let u1 =
                    FStar_TypeChecker_Normalize.normalize_universe env u  in
                  let v2 =
                    FStar_TypeChecker_Normalize.normalize_universe env v1  in
                  (match (u1, v2) with
                   | (FStar_Syntax_Syntax.U_zero ,uu____31222) -> true
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
                      uu____31246,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_unif
                      uu____31248,FStar_Syntax_Syntax.U_succ v0) ->
                       check_ineq (u1, v0)
                   | (FStar_Syntax_Syntax.U_max us,uu____31259) ->
                       FStar_All.pipe_right us
                         (FStar_Util.for_all (fun u2  -> check_ineq (u2, v2)))
                   | (uu____31267,FStar_Syntax_Syntax.U_max vs) ->
                       FStar_All.pipe_right vs
                         (FStar_Util.for_some
                            (fun v3  -> check_ineq (u1, v3)))
                   | uu____31276 -> false)
               in
            let uu____31282 =
              FStar_All.pipe_right ineqs
                (FStar_Util.for_all
                   (fun uu____31299  ->
                      match uu____31299 with
                      | (u,v1) ->
                          let uu____31307 = check_ineq (u, v1)  in
                          if uu____31307
                          then true
                          else
                            ((let uu____31315 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "GenUniverses")
                                 in
                              if uu____31315
                              then
                                let uu____31320 =
                                  FStar_Syntax_Print.univ_to_string u  in
                                let uu____31322 =
                                  FStar_Syntax_Print.univ_to_string v1  in
                                FStar_Util.print2 "%s </= %s" uu____31320
                                  uu____31322
                              else ());
                             false)))
               in
            if uu____31282
            then ()
            else
              ((let uu____31332 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "GenUniverses")
                   in
                if uu____31332
                then
                  ((let uu____31338 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Partially solved inequality constraints are: %s\n"
                      uu____31338);
                   FStar_Syntax_Unionfind.rollback tx;
                   (let uu____31350 = ineqs_to_string (variables, ineqs)  in
                    FStar_Util.print1
                      "Original solved inequality constraints are: %s\n"
                      uu____31350))
                else ());
               (let uu____31363 = FStar_TypeChecker_Env.get_range env  in
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_FailToSolveUniverseInEquality,
                    "Failed to solve universe inequalities for inductives")
                  uu____31363))
  
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
        let fail1 uu____31438 =
          match uu____31438 with
          | (d,s) ->
              let msg = explain env d s  in
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_ErrorInSolveDeferredConstraints, msg)
                (p_loc d)
           in
        let wl =
          let uu___4196_31465 =
            wl_of_guard env g.FStar_TypeChecker_Common.deferred  in
          {
            attempting = (uu___4196_31465.attempting);
            wl_deferred = (uu___4196_31465.wl_deferred);
            wl_deferred_to_tac = (uu___4196_31465.wl_deferred_to_tac);
            ctr = (uu___4196_31465.ctr);
            defer_ok;
            smt_ok = (uu___4196_31465.smt_ok);
            umax_heuristic_ok = (uu___4196_31465.umax_heuristic_ok);
            tcenv = (uu___4196_31465.tcenv);
            wl_implicits = (uu___4196_31465.wl_implicits)
          }  in
        (let uu____31468 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____31468
         then
           let uu____31473 = FStar_Util.string_of_bool defer_ok  in
           let uu____31475 = wl_to_string wl  in
           let uu____31477 =
             FStar_Util.string_of_int
               (FStar_List.length g.FStar_TypeChecker_Common.implicits)
              in
           FStar_Util.print3
             "Trying to solve carried problems (defer_ok=%s): begin\n\t%s\nend\n and %s implicits\n"
             uu____31473 uu____31475 uu____31477
         else ());
        (let g1 =
           let uu____31483 = solve_and_commit env wl fail1  in
           match uu____31483 with
           | FStar_Pervasives_Native.Some
               (uu____31492::uu____31493,uu____31494,uu____31495) when
               Prims.op_Negation defer_ok ->
               failwith "Impossible: Unexpected deferred constraints remain"
           | FStar_Pervasives_Native.Some (deferred,defer_to_tac,imps) ->
               let uu___4213_31529 = g  in
               {
                 FStar_TypeChecker_Common.guard_f =
                   (uu___4213_31529.FStar_TypeChecker_Common.guard_f);
                 FStar_TypeChecker_Common.deferred_to_tac =
                   (FStar_List.append
                      g.FStar_TypeChecker_Common.deferred_to_tac defer_to_tac);
                 FStar_TypeChecker_Common.deferred = deferred;
                 FStar_TypeChecker_Common.univ_ineqs =
                   (uu___4213_31529.FStar_TypeChecker_Common.univ_ineqs);
                 FStar_TypeChecker_Common.implicits =
                   (FStar_List.append g.FStar_TypeChecker_Common.implicits
                      imps)
               }
           | uu____31535 ->
               failwith "Impossible: should have raised a failure already"
            in
         solve_universe_inequalities env
           g1.FStar_TypeChecker_Common.univ_ineqs;
         (let uu___4218_31546 = g1  in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4218_31546.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4218_31546.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4218_31546.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs = ([], []);
            FStar_TypeChecker_Common.implicits =
              (uu___4218_31546.FStar_TypeChecker_Common.implicits)
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
          (let uu____31622 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "ResolveImplicitsHook")
              in
           if uu____31622
           then
             let uu____31627 = guard_to_string env g  in
             FStar_Util.print1
               "///////////////////ResolveImplicitsHook: discharge_guard'\nguard = %s\n"
               uu____31627
           else ());
          (let g1 = solve_deferred_constraints env g  in
           let ret_g =
             let uu___4232_31634 = g1  in
             {
               FStar_TypeChecker_Common.guard_f =
                 FStar_TypeChecker_Common.Trivial;
               FStar_TypeChecker_Common.deferred_to_tac =
                 (uu___4232_31634.FStar_TypeChecker_Common.deferred_to_tac);
               FStar_TypeChecker_Common.deferred =
                 (uu___4232_31634.FStar_TypeChecker_Common.deferred);
               FStar_TypeChecker_Common.univ_ineqs =
                 (uu___4232_31634.FStar_TypeChecker_Common.univ_ineqs);
               FStar_TypeChecker_Common.implicits =
                 (uu___4232_31634.FStar_TypeChecker_Common.implicits)
             }  in
           let uu____31635 =
             let uu____31637 = FStar_TypeChecker_Env.should_verify env  in
             Prims.op_Negation uu____31637  in
           if uu____31635
           then FStar_Pervasives_Native.Some ret_g
           else
             (match g1.FStar_TypeChecker_Common.guard_f with
              | FStar_TypeChecker_Common.Trivial  ->
                  FStar_Pervasives_Native.Some ret_g
              | FStar_TypeChecker_Common.NonTrivial vc ->
                  (if debug1
                   then
                     (let uu____31649 = FStar_TypeChecker_Env.get_range env
                         in
                      let uu____31650 =
                        let uu____31652 =
                          FStar_Syntax_Print.term_to_string vc  in
                        FStar_Util.format1 "Before normalization VC=\n%s\n"
                          uu____31652
                         in
                      FStar_Errors.diag uu____31649 uu____31650)
                   else ();
                   (let vc1 =
                      let uu____31658 =
                        let uu____31662 =
                          let uu____31664 =
                            FStar_TypeChecker_Env.current_module env  in
                          FStar_Ident.string_of_lid uu____31664  in
                        FStar_Pervasives_Native.Some uu____31662  in
                      FStar_Profiling.profile
                        (fun uu____31667  ->
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.Eager_unfolding;
                             FStar_TypeChecker_Env.Simplify;
                             FStar_TypeChecker_Env.Primops] env vc)
                        uu____31658 "FStar.TypeChecker.Rel.vc_normalization"
                       in
                    if debug1
                    then
                      (let uu____31671 = FStar_TypeChecker_Env.get_range env
                          in
                       let uu____31672 =
                         let uu____31674 =
                           FStar_Syntax_Print.term_to_string vc1  in
                         FStar_Util.format1 "After normalization VC=\n%s\n"
                           uu____31674
                          in
                       FStar_Errors.diag uu____31671 uu____31672)
                    else ();
                    (let uu____31680 = FStar_TypeChecker_Env.get_range env
                        in
                     FStar_TypeChecker_Env.def_check_closed_in_env
                       uu____31680 "discharge_guard'" env vc1);
                    (let uu____31682 =
                       FStar_TypeChecker_Common.check_trivial vc1  in
                     match uu____31682 with
                     | FStar_TypeChecker_Common.Trivial  ->
                         FStar_Pervasives_Native.Some ret_g
                     | FStar_TypeChecker_Common.NonTrivial vc2 ->
                         if Prims.op_Negation use_smt
                         then
                           (if debug1
                            then
                              (let uu____31691 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31692 =
                                 let uu____31694 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1
                                   "Cannot solve without SMT : %s\n"
                                   uu____31694
                                  in
                               FStar_Errors.diag uu____31691 uu____31692)
                            else ();
                            FStar_Pervasives_Native.None)
                         else
                           (if debug1
                            then
                              (let uu____31704 =
                                 FStar_TypeChecker_Env.get_range env  in
                               let uu____31705 =
                                 let uu____31707 =
                                   FStar_Syntax_Print.term_to_string vc2  in
                                 FStar_Util.format1 "Checking VC=\n%s\n"
                                   uu____31707
                                  in
                               FStar_Errors.diag uu____31704 uu____31705)
                            else ();
                            (let vcs =
                               let uu____31721 = FStar_Options.use_tactics ()
                                  in
                               if uu____31721
                               then
                                 FStar_Options.with_saved_options
                                   (fun uu____31743  ->
                                      (let uu____31745 =
                                         FStar_Options.set_options
                                           "--no_tactics"
                                          in
                                       FStar_All.pipe_left (fun a1  -> ())
                                         uu____31745);
                                      (let vcs =
                                         (env.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.preprocess
                                           env vc2
                                          in
                                       FStar_All.pipe_right vcs
                                         (FStar_List.map
                                            (fun uu____31789  ->
                                               match uu____31789 with
                                               | (env1,goal,opts) ->
                                                   let uu____31805 =
                                                     norm_with_steps
                                                       "FStar.TypeChecker.Rel.norm_with_steps.7"
                                                       [FStar_TypeChecker_Env.Simplify;
                                                       FStar_TypeChecker_Env.Primops]
                                                       env1 goal
                                                      in
                                                   (env1, uu____31805, opts)))))
                               else
                                 (let uu____31809 =
                                    let uu____31816 = FStar_Options.peek ()
                                       in
                                    (env, vc2, uu____31816)  in
                                  [uu____31809])
                                in
                             FStar_All.pipe_right vcs
                               (FStar_List.iter
                                  (fun uu____31849  ->
                                     match uu____31849 with
                                     | (env1,goal,opts) ->
                                         let uu____31859 =
                                           FStar_TypeChecker_Common.check_trivial
                                             goal
                                            in
                                         (match uu____31859 with
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
                                                 (let uu____31870 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31871 =
                                                    let uu____31873 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    let uu____31875 =
                                                      FStar_TypeChecker_Env.string_of_proof_ns
                                                        env1
                                                       in
                                                    FStar_Util.format2
                                                      "Trying to solve:\n> %s\nWith proof_ns:\n %s\n"
                                                      uu____31873 uu____31875
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31870 uu____31871)
                                               else ();
                                               if debug1
                                               then
                                                 (let uu____31882 =
                                                    FStar_TypeChecker_Env.get_range
                                                      env1
                                                     in
                                                  let uu____31883 =
                                                    let uu____31885 =
                                                      FStar_Syntax_Print.term_to_string
                                                        goal1
                                                       in
                                                    FStar_Util.format1
                                                      "Before calling solver VC=\n%s\n"
                                                      uu____31885
                                                     in
                                                  FStar_Errors.diag
                                                    uu____31882 uu____31883)
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
      let uu____31903 =
        discharge_guard' FStar_Pervasives_Native.None env g false  in
      match uu____31903 with
      | FStar_Pervasives_Native.Some g1 -> g1
      | FStar_Pervasives_Native.None  ->
          let uu____31912 = FStar_TypeChecker_Env.get_range env  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExpectTrivialPreCondition,
              "Expected a trivial pre-condition") uu____31912
  
let (discharge_guard :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      let uu____31926 =
        discharge_guard' FStar_Pervasives_Native.None env g true  in
      match uu____31926 with
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
        let uu____31956 = try_teq false env t1 t2  in
        match uu____31956 with
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
            let uu____32000 =
              FStar_Syntax_Unionfind.find
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
               in
            match uu____32000 with
            | FStar_Pervasives_Native.Some r ->
                (match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta with
                 | FStar_Pervasives_Native.None  -> false
                 | FStar_Pervasives_Native.Some uu____32007 ->
                     let uu____32008 =
                       let uu____32009 = FStar_Syntax_Subst.compress r  in
                       uu____32009.FStar_Syntax_Syntax.n  in
                     (match uu____32008 with
                      | FStar_Syntax_Syntax.Tm_uvar (ctx_u',uu____32014) ->
                          unresolved ctx_u'
                      | uu____32031 -> false))
            | FStar_Pervasives_Native.None  -> true  in
          let rec until_fixpoint acc implicits =
            let uu____32055 = acc  in
            match uu____32055 with
            | (out,changed) ->
                (match implicits with
                 | [] ->
                     if Prims.op_Negation changed
                     then out
                     else until_fixpoint ([], false) out
                 | hd1::tl1 ->
                     let uu____32074 = hd1  in
                     (match uu____32074 with
                      | { FStar_TypeChecker_Common.imp_reason = reason;
                          FStar_TypeChecker_Common.imp_uvar = ctx_u;
                          FStar_TypeChecker_Common.imp_tm = tm;
                          FStar_TypeChecker_Common.imp_range = r;_} ->
                          if
                            ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check =
                              FStar_Syntax_Syntax.Allow_unresolved
                          then until_fixpoint (out, true) tl1
                          else
                            (let uu____32085 = unresolved ctx_u  in
                             if uu____32085
                             then
                               match ctx_u.FStar_Syntax_Syntax.ctx_uvar_meta
                               with
                               | FStar_Pervasives_Native.Some
                                   (FStar_Syntax_Syntax.Ctx_uvar_meta_tac
                                   (env_dyn,tau)) ->
                                   let env1 = FStar_Dyn.undyn env_dyn  in
                                   ((let uu____32096 =
                                       FStar_TypeChecker_Env.debug env1
                                         (FStar_Options.Other "Tac")
                                        in
                                     if uu____32096
                                     then
                                       let uu____32100 =
                                         FStar_Syntax_Print.ctx_uvar_to_string
                                           ctx_u
                                          in
                                       FStar_Util.print1
                                         "Running tactic for meta-arg %s\n"
                                         uu____32100
                                     else ());
                                    (let t =
                                       env1.FStar_TypeChecker_Env.synth_hook
                                         env1
                                         (hd1.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                                         tau
                                        in
                                     let extra =
                                       let uu____32109 = teq_nosmt env1 t tm
                                          in
                                       match uu____32109 with
                                       | FStar_Pervasives_Native.None  ->
                                           failwith
                                             "resolve_implicits: unifying with an unresolved uvar failed?"
                                       | FStar_Pervasives_Native.Some g1 ->
                                           g1.FStar_TypeChecker_Common.implicits
                                        in
                                     let ctx_u1 =
                                       let uu___4345_32119 = ctx_u  in
                                       {
                                         FStar_Syntax_Syntax.ctx_uvar_head =
                                           (uu___4345_32119.FStar_Syntax_Syntax.ctx_uvar_head);
                                         FStar_Syntax_Syntax.ctx_uvar_gamma =
                                           (uu___4345_32119.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                         FStar_Syntax_Syntax.ctx_uvar_binders
                                           =
                                           (uu___4345_32119.FStar_Syntax_Syntax.ctx_uvar_binders);
                                         FStar_Syntax_Syntax.ctx_uvar_typ =
                                           (uu___4345_32119.FStar_Syntax_Syntax.ctx_uvar_typ);
                                         FStar_Syntax_Syntax.ctx_uvar_reason
                                           =
                                           (uu___4345_32119.FStar_Syntax_Syntax.ctx_uvar_reason);
                                         FStar_Syntax_Syntax.ctx_uvar_should_check
                                           =
                                           (uu___4345_32119.FStar_Syntax_Syntax.ctx_uvar_should_check);
                                         FStar_Syntax_Syntax.ctx_uvar_range =
                                           (uu___4345_32119.FStar_Syntax_Syntax.ctx_uvar_range);
                                         FStar_Syntax_Syntax.ctx_uvar_meta =
                                           FStar_Pervasives_Native.None
                                       }  in
                                     let hd2 =
                                       let uu___4348_32121 = hd1  in
                                       {
                                         FStar_TypeChecker_Common.imp_reason
                                           =
                                           (uu___4348_32121.FStar_TypeChecker_Common.imp_reason);
                                         FStar_TypeChecker_Common.imp_uvar =
                                           ctx_u1;
                                         FStar_TypeChecker_Common.imp_tm =
                                           (uu___4348_32121.FStar_TypeChecker_Common.imp_tm);
                                         FStar_TypeChecker_Common.imp_range =
                                           (uu___4348_32121.FStar_TypeChecker_Common.imp_range)
                                       }  in
                                     until_fixpoint (out, true)
                                       (FStar_List.append extra tl1)))
                               | uu____32124 ->
                                   until_fixpoint ((hd1 :: out), changed) tl1
                             else
                               if
                                 ctx_u.FStar_Syntax_Syntax.ctx_uvar_should_check
                                   = FStar_Syntax_Syntax.Allow_untyped
                               then until_fixpoint (out, true) tl1
                               else
                                 (let env1 =
                                    let uu___4353_32136 = env  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___4353_32136.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___4353_32136.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___4353_32136.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (ctx_u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___4353_32136.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___4353_32136.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___4353_32136.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___4353_32136.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___4353_32136.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___4353_32136.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___4353_32136.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___4353_32136.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___4353_32136.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___4353_32136.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___4353_32136.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___4353_32136.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___4353_32136.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___4353_32136.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___4353_32136.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___4353_32136.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___4353_32136.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___4353_32136.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___4353_32136.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___4353_32136.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___4353_32136.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___4353_32136.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___4353_32136.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___4353_32136.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___4353_32136.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___4353_32136.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___4353_32136.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___4353_32136.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___4353_32136.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___4353_32136.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___4353_32136.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___4353_32136.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___4353_32136.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___4353_32136.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___4353_32136.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___4353_32136.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___4353_32136.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___4353_32136.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___4353_32136.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___4353_32136.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___4353_32136.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___4353_32136.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___4353_32136.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___4353_32136.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  let tm1 =
                                    norm_with_steps
                                      "FStar.TypeChecker.Rel.norm_with_steps.8"
                                      [FStar_TypeChecker_Env.Beta] env1 tm
                                     in
                                  let env2 =
                                    if forcelax
                                    then
                                      let uu___4358_32141 = env1  in
                                      {
                                        FStar_TypeChecker_Env.solver =
                                          (uu___4358_32141.FStar_TypeChecker_Env.solver);
                                        FStar_TypeChecker_Env.range =
                                          (uu___4358_32141.FStar_TypeChecker_Env.range);
                                        FStar_TypeChecker_Env.curmodule =
                                          (uu___4358_32141.FStar_TypeChecker_Env.curmodule);
                                        FStar_TypeChecker_Env.gamma =
                                          (uu___4358_32141.FStar_TypeChecker_Env.gamma);
                                        FStar_TypeChecker_Env.gamma_sig =
                                          (uu___4358_32141.FStar_TypeChecker_Env.gamma_sig);
                                        FStar_TypeChecker_Env.gamma_cache =
                                          (uu___4358_32141.FStar_TypeChecker_Env.gamma_cache);
                                        FStar_TypeChecker_Env.modules =
                                          (uu___4358_32141.FStar_TypeChecker_Env.modules);
                                        FStar_TypeChecker_Env.expected_typ =
                                          (uu___4358_32141.FStar_TypeChecker_Env.expected_typ);
                                        FStar_TypeChecker_Env.sigtab =
                                          (uu___4358_32141.FStar_TypeChecker_Env.sigtab);
                                        FStar_TypeChecker_Env.attrtab =
                                          (uu___4358_32141.FStar_TypeChecker_Env.attrtab);
                                        FStar_TypeChecker_Env.instantiate_imp
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.instantiate_imp);
                                        FStar_TypeChecker_Env.effects =
                                          (uu___4358_32141.FStar_TypeChecker_Env.effects);
                                        FStar_TypeChecker_Env.generalize =
                                          (uu___4358_32141.FStar_TypeChecker_Env.generalize);
                                        FStar_TypeChecker_Env.letrecs =
                                          (uu___4358_32141.FStar_TypeChecker_Env.letrecs);
                                        FStar_TypeChecker_Env.top_level =
                                          (uu___4358_32141.FStar_TypeChecker_Env.top_level);
                                        FStar_TypeChecker_Env.check_uvars =
                                          (uu___4358_32141.FStar_TypeChecker_Env.check_uvars);
                                        FStar_TypeChecker_Env.use_eq =
                                          (uu___4358_32141.FStar_TypeChecker_Env.use_eq);
                                        FStar_TypeChecker_Env.use_eq_strict =
                                          (uu___4358_32141.FStar_TypeChecker_Env.use_eq_strict);
                                        FStar_TypeChecker_Env.is_iface =
                                          (uu___4358_32141.FStar_TypeChecker_Env.is_iface);
                                        FStar_TypeChecker_Env.admit =
                                          (uu___4358_32141.FStar_TypeChecker_Env.admit);
                                        FStar_TypeChecker_Env.lax = true;
                                        FStar_TypeChecker_Env.lax_universes =
                                          (uu___4358_32141.FStar_TypeChecker_Env.lax_universes);
                                        FStar_TypeChecker_Env.phase1 =
                                          (uu___4358_32141.FStar_TypeChecker_Env.phase1);
                                        FStar_TypeChecker_Env.failhard =
                                          (uu___4358_32141.FStar_TypeChecker_Env.failhard);
                                        FStar_TypeChecker_Env.nosynth =
                                          (uu___4358_32141.FStar_TypeChecker_Env.nosynth);
                                        FStar_TypeChecker_Env.uvar_subtyping
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.uvar_subtyping);
                                        FStar_TypeChecker_Env.tc_term =
                                          (uu___4358_32141.FStar_TypeChecker_Env.tc_term);
                                        FStar_TypeChecker_Env.type_of =
                                          (uu___4358_32141.FStar_TypeChecker_Env.type_of);
                                        FStar_TypeChecker_Env.universe_of =
                                          (uu___4358_32141.FStar_TypeChecker_Env.universe_of);
                                        FStar_TypeChecker_Env.check_type_of =
                                          (uu___4358_32141.FStar_TypeChecker_Env.check_type_of);
                                        FStar_TypeChecker_Env.use_bv_sorts =
                                          (uu___4358_32141.FStar_TypeChecker_Env.use_bv_sorts);
                                        FStar_TypeChecker_Env.qtbl_name_and_index
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.qtbl_name_and_index);
                                        FStar_TypeChecker_Env.normalized_eff_names
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.normalized_eff_names);
                                        FStar_TypeChecker_Env.fv_delta_depths
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.fv_delta_depths);
                                        FStar_TypeChecker_Env.proof_ns =
                                          (uu___4358_32141.FStar_TypeChecker_Env.proof_ns);
                                        FStar_TypeChecker_Env.synth_hook =
                                          (uu___4358_32141.FStar_TypeChecker_Env.synth_hook);
                                        FStar_TypeChecker_Env.try_solve_implicits_hook
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                        FStar_TypeChecker_Env.splice =
                                          (uu___4358_32141.FStar_TypeChecker_Env.splice);
                                        FStar_TypeChecker_Env.mpreprocess =
                                          (uu___4358_32141.FStar_TypeChecker_Env.mpreprocess);
                                        FStar_TypeChecker_Env.postprocess =
                                          (uu___4358_32141.FStar_TypeChecker_Env.postprocess);
                                        FStar_TypeChecker_Env.is_native_tactic
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.is_native_tactic);
                                        FStar_TypeChecker_Env.identifier_info
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.identifier_info);
                                        FStar_TypeChecker_Env.tc_hooks =
                                          (uu___4358_32141.FStar_TypeChecker_Env.tc_hooks);
                                        FStar_TypeChecker_Env.dsenv =
                                          (uu___4358_32141.FStar_TypeChecker_Env.dsenv);
                                        FStar_TypeChecker_Env.nbe =
                                          (uu___4358_32141.FStar_TypeChecker_Env.nbe);
                                        FStar_TypeChecker_Env.strict_args_tab
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.strict_args_tab);
                                        FStar_TypeChecker_Env.erasable_types_tab
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.erasable_types_tab);
                                        FStar_TypeChecker_Env.enable_defer_to_tac
                                          =
                                          (uu___4358_32141.FStar_TypeChecker_Env.enable_defer_to_tac)
                                      }
                                    else env1  in
                                  (let uu____32146 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Rel")
                                      in
                                   if uu____32146
                                   then
                                     let uu____32151 =
                                       FStar_Syntax_Print.uvar_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                        in
                                     let uu____32153 =
                                       FStar_Syntax_Print.term_to_string tm1
                                        in
                                     let uu____32155 =
                                       FStar_Syntax_Print.term_to_string
                                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                        in
                                     let uu____32157 =
                                       FStar_Range.string_of_range r  in
                                     FStar_Util.print5
                                       "Checking uvar %s resolved to %s at type %s, introduce for %s at %s\n"
                                       uu____32151 uu____32153 uu____32155
                                       reason uu____32157
                                   else ());
                                  (let g1 =
                                     try
                                       (fun uu___4364_32164  ->
                                          match () with
                                          | () ->
                                              env2.FStar_TypeChecker_Env.check_type_of
                                                must_total env2 tm1
                                                ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ)
                                         ()
                                     with
                                     | e when FStar_Errors.handleable e ->
                                         ((let uu____32171 =
                                             let uu____32181 =
                                               let uu____32189 =
                                                 let uu____32191 =
                                                   FStar_Syntax_Print.uvar_to_string
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_head
                                                    in
                                                 let uu____32193 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2 tm1
                                                    in
                                                 let uu____32195 =
                                                   FStar_TypeChecker_Normalize.term_to_string
                                                     env2
                                                     ctx_u.FStar_Syntax_Syntax.ctx_uvar_typ
                                                    in
                                                 FStar_Util.format3
                                                   "Failed while checking implicit %s set to %s of expected type %s"
                                                   uu____32191 uu____32193
                                                   uu____32195
                                                  in
                                               (FStar_Errors.Error_BadImplicit,
                                                 uu____32189, r)
                                                in
                                             [uu____32181]  in
                                           FStar_Errors.add_errors
                                             uu____32171);
                                          FStar_Exn.raise e)
                                      in
                                   let g' =
                                     let uu____32214 =
                                       discharge_guard'
                                         (FStar_Pervasives_Native.Some
                                            (fun uu____32225  ->
                                               let uu____32226 =
                                                 FStar_Syntax_Print.term_to_string
                                                   tm1
                                                  in
                                               let uu____32228 =
                                                 FStar_Range.string_of_range
                                                   r
                                                  in
                                               let uu____32230 =
                                                 FStar_Range.string_of_range
                                                   tm1.FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Util.format4
                                                 "%s (Introduced at %s for %s resolved at %s)"
                                                 uu____32226 uu____32228
                                                 reason uu____32230)) env2 g1
                                         true
                                        in
                                     match uu____32214 with
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
          let uu___4376_32238 = g  in
          let uu____32239 =
            until_fixpoint ([], false) g.FStar_TypeChecker_Common.implicits
             in
          {
            FStar_TypeChecker_Common.guard_f =
              (uu___4376_32238.FStar_TypeChecker_Common.guard_f);
            FStar_TypeChecker_Common.deferred_to_tac =
              (uu___4376_32238.FStar_TypeChecker_Common.deferred_to_tac);
            FStar_TypeChecker_Common.deferred =
              (uu___4376_32238.FStar_TypeChecker_Common.deferred);
            FStar_TypeChecker_Common.univ_ineqs =
              (uu___4376_32238.FStar_TypeChecker_Common.univ_ineqs);
            FStar_TypeChecker_Common.implicits = uu____32239
          }
  
let (resolve_implicits :
  FStar_TypeChecker_Env.env ->
    FStar_TypeChecker_Common.guard_t -> FStar_TypeChecker_Common.guard_t)
  =
  fun env  ->
    fun g  ->
      (let uu____32254 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32254
       then
         let uu____32259 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: resolve_implicits////////////\nguard = %s\n"
           uu____32259
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
      (let uu____32290 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "ResolveImplicitsHook")
          in
       if uu____32290
       then
         let uu____32295 = guard_to_string env g  in
         FStar_Util.print1
           "//////////////////////////ResolveImplicitsHook: force_trivial_guard////////////\nguard = %s\n"
           uu____32295
       else ());
      (let solve_deferred_to_tactic g1 =
         let deferred = g1.FStar_TypeChecker_Common.deferred_to_tac  in
         match deferred with
         | [] -> g1
         | uu____32312 ->
             let prob_as_implicit uu____32323 =
               match uu____32323 with
               | (reason,prob) ->
                   (match prob with
                    | FStar_TypeChecker_Common.TProb tp when
                        tp.FStar_TypeChecker_Common.relation =
                          FStar_TypeChecker_Common.EQ
                        ->
                        let env1 =
                          let uu___4399_32337 = env  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4399_32337.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4399_32337.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4399_32337.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              ((tp.FStar_TypeChecker_Common.logical_guard_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4399_32337.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4399_32337.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4399_32337.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4399_32337.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4399_32337.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4399_32337.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4399_32337.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4399_32337.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4399_32337.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4399_32337.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4399_32337.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4399_32337.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4399_32337.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4399_32337.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4399_32337.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4399_32337.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax =
                              (uu___4399_32337.FStar_TypeChecker_Env.lax);
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4399_32337.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4399_32337.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4399_32337.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4399_32337.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4399_32337.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4399_32337.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4399_32337.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4399_32337.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4399_32337.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___4399_32337.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4399_32337.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4399_32337.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4399_32337.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4399_32337.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4399_32337.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4399_32337.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4399_32337.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4399_32337.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4399_32337.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___4399_32337.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4399_32337.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4399_32337.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4399_32337.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4399_32337.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4399_32337.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4399_32337.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4399_32337.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let env_lax =
                          let uu___4402_32339 = env1  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___4402_32339.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___4402_32339.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___4402_32339.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___4402_32339.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___4402_32339.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___4402_32339.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___4402_32339.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___4402_32339.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___4402_32339.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___4402_32339.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___4402_32339.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___4402_32339.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___4402_32339.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___4402_32339.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___4402_32339.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___4402_32339.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___4402_32339.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.use_eq_strict =
                              (uu___4402_32339.FStar_TypeChecker_Env.use_eq_strict);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___4402_32339.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___4402_32339.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___4402_32339.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___4402_32339.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___4402_32339.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___4402_32339.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___4402_32339.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___4402_32339.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___4402_32339.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___4402_32339.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___4402_32339.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts = true;
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___4402_32339.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___4402_32339.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___4402_32339.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___4402_32339.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___4402_32339.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___4402_32339.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___4402_32339.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.mpreprocess =
                              (uu___4402_32339.FStar_TypeChecker_Env.mpreprocess);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___4402_32339.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___4402_32339.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___4402_32339.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___4402_32339.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___4402_32339.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___4402_32339.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___4402_32339.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___4402_32339.FStar_TypeChecker_Env.erasable_types_tab);
                            FStar_TypeChecker_Env.enable_defer_to_tac =
                              (uu___4402_32339.FStar_TypeChecker_Env.enable_defer_to_tac)
                          }  in
                        let uu____32342 =
                          env1.FStar_TypeChecker_Env.type_of env_lax
                            tp.FStar_TypeChecker_Common.lhs
                           in
                        (match uu____32342 with
                         | (uu____32349,tlhs,uu____32351) ->
                             let goal_ty =
                               let uu____32353 =
                                 env1.FStar_TypeChecker_Env.universe_of
                                   env_lax tlhs
                                  in
                               FStar_Syntax_Util.mk_eq2 uu____32353 tlhs
                                 tp.FStar_TypeChecker_Common.lhs
                                 tp.FStar_TypeChecker_Common.rhs
                                in
                             let uu____32354 =
                               FStar_TypeChecker_Env.new_implicit_var_aux
                                 reason
                                 (tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos
                                 env1 goal_ty
                                 FStar_Syntax_Syntax.Allow_untyped
                                 FStar_Pervasives_Native.None
                                in
                             (match uu____32354 with
                              | (goal,ctx_uvar,uu____32369) ->
                                  let uu____32382 =
                                    let uu____32383 = FStar_List.hd ctx_uvar
                                       in
                                    FStar_Pervasives_Native.fst uu____32383
                                     in
                                  {
                                    FStar_TypeChecker_Common.imp_reason = "";
                                    FStar_TypeChecker_Common.imp_uvar =
                                      uu____32382;
                                    FStar_TypeChecker_Common.imp_tm = goal;
                                    FStar_TypeChecker_Common.imp_range =
                                      ((tp.FStar_TypeChecker_Common.lhs).FStar_Syntax_Syntax.pos)
                                  }))
                    | uu____32393 ->
                        failwith "Unexpected problem deferred to tactic")
                in
             let deferred_goals =
               FStar_List.map prob_as_implicit
                 g1.FStar_TypeChecker_Common.deferred_to_tac
                in
             let uu____32403 =
               FStar_List.partition
                 (fun imp  ->
                    let uu____32415 =
                      FStar_Syntax_Unionfind.find
                        (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                       in
                    match uu____32415 with
                    | FStar_Pervasives_Native.None  -> true
                    | uu____32420 -> false)
                 g1.FStar_TypeChecker_Common.implicits
                in
             (match uu____32403 with
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
                                  let uu____32447 =
                                    FStar_Syntax_Print.term_to_string a  in
                                  FStar_Util.format2 "%s::%s" uu____32447
                                    i.FStar_TypeChecker_Common.imp_reason
                                   in
                                let uu___4427_32450 = i  in
                                {
                                  FStar_TypeChecker_Common.imp_reason =
                                    reason;
                                  FStar_TypeChecker_Common.imp_uvar =
                                    (uu___4427_32450.FStar_TypeChecker_Common.imp_uvar);
                                  FStar_TypeChecker_Common.imp_tm =
                                    (uu___4427_32450.FStar_TypeChecker_Common.imp_tm);
                                  FStar_TypeChecker_Common.imp_range =
                                    (uu___4427_32450.FStar_TypeChecker_Common.imp_range)
                                }
                            | uu____32451 -> i))
                     in
                  let deferred_goals1 =
                    FStar_TypeChecker_DeferredImplicits.sort_goals env
                      deferred_goals more1
                     in
                  let guard =
                    let uu___4432_32456 = g1  in
                    {
                      FStar_TypeChecker_Common.guard_f =
                        (uu___4432_32456.FStar_TypeChecker_Common.guard_f);
                      FStar_TypeChecker_Common.deferred_to_tac = [];
                      FStar_TypeChecker_Common.deferred =
                        (uu___4432_32456.FStar_TypeChecker_Common.deferred);
                      FStar_TypeChecker_Common.univ_ineqs =
                        (uu___4432_32456.FStar_TypeChecker_Common.univ_ineqs);
                      FStar_TypeChecker_Common.implicits = imps
                    }  in
                  let resolve_tac =
                    let uu____32463 =
                      FStar_TypeChecker_Env.lookup_attr env
                        FStar_Parser_Const.resolve_implicits_attr_string
                       in
                    match uu____32463 with
                    | {
                        FStar_Syntax_Syntax.sigel =
                          FStar_Syntax_Syntax.Sig_let (uu____32466,lid::[]);
                        FStar_Syntax_Syntax.sigrng = uu____32468;
                        FStar_Syntax_Syntax.sigquals = uu____32469;
                        FStar_Syntax_Syntax.sigmeta = uu____32470;
                        FStar_Syntax_Syntax.sigattrs = uu____32471;
                        FStar_Syntax_Syntax.sigopts = uu____32472;_}::uu____32473
                        ->
                        let qn = FStar_TypeChecker_Env.lookup_qname env lid
                           in
                        let fv =
                          FStar_Syntax_Syntax.lid_as_fv lid
                            (FStar_Syntax_Syntax.Delta_constant_at_level
                               Prims.int_zero) FStar_Pervasives_Native.None
                           in
                        let dd =
                          let uu____32488 =
                            FStar_TypeChecker_Env.delta_depth_of_qninfo fv qn
                             in
                          match uu____32488 with
                          | FStar_Pervasives_Native.Some dd -> dd
                          | FStar_Pervasives_Native.None  ->
                              failwith "Expected a dd"
                           in
                        let term =
                          let uu____32494 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Syntax_Syntax.fv_to_tm uu____32494  in
                        term
                    | uu____32495 -> failwith "Resolve_tac not found"  in
                  let env1 =
                    let uu___4457_32500 = env  in
                    {
                      FStar_TypeChecker_Env.solver =
                        (uu___4457_32500.FStar_TypeChecker_Env.solver);
                      FStar_TypeChecker_Env.range =
                        (uu___4457_32500.FStar_TypeChecker_Env.range);
                      FStar_TypeChecker_Env.curmodule =
                        (uu___4457_32500.FStar_TypeChecker_Env.curmodule);
                      FStar_TypeChecker_Env.gamma =
                        (uu___4457_32500.FStar_TypeChecker_Env.gamma);
                      FStar_TypeChecker_Env.gamma_sig =
                        (uu___4457_32500.FStar_TypeChecker_Env.gamma_sig);
                      FStar_TypeChecker_Env.gamma_cache =
                        (uu___4457_32500.FStar_TypeChecker_Env.gamma_cache);
                      FStar_TypeChecker_Env.modules =
                        (uu___4457_32500.FStar_TypeChecker_Env.modules);
                      FStar_TypeChecker_Env.expected_typ =
                        (uu___4457_32500.FStar_TypeChecker_Env.expected_typ);
                      FStar_TypeChecker_Env.sigtab =
                        (uu___4457_32500.FStar_TypeChecker_Env.sigtab);
                      FStar_TypeChecker_Env.attrtab =
                        (uu___4457_32500.FStar_TypeChecker_Env.attrtab);
                      FStar_TypeChecker_Env.instantiate_imp =
                        (uu___4457_32500.FStar_TypeChecker_Env.instantiate_imp);
                      FStar_TypeChecker_Env.effects =
                        (uu___4457_32500.FStar_TypeChecker_Env.effects);
                      FStar_TypeChecker_Env.generalize =
                        (uu___4457_32500.FStar_TypeChecker_Env.generalize);
                      FStar_TypeChecker_Env.letrecs =
                        (uu___4457_32500.FStar_TypeChecker_Env.letrecs);
                      FStar_TypeChecker_Env.top_level =
                        (uu___4457_32500.FStar_TypeChecker_Env.top_level);
                      FStar_TypeChecker_Env.check_uvars =
                        (uu___4457_32500.FStar_TypeChecker_Env.check_uvars);
                      FStar_TypeChecker_Env.use_eq =
                        (uu___4457_32500.FStar_TypeChecker_Env.use_eq);
                      FStar_TypeChecker_Env.use_eq_strict =
                        (uu___4457_32500.FStar_TypeChecker_Env.use_eq_strict);
                      FStar_TypeChecker_Env.is_iface =
                        (uu___4457_32500.FStar_TypeChecker_Env.is_iface);
                      FStar_TypeChecker_Env.admit =
                        (uu___4457_32500.FStar_TypeChecker_Env.admit);
                      FStar_TypeChecker_Env.lax =
                        (uu___4457_32500.FStar_TypeChecker_Env.lax);
                      FStar_TypeChecker_Env.lax_universes =
                        (uu___4457_32500.FStar_TypeChecker_Env.lax_universes);
                      FStar_TypeChecker_Env.phase1 =
                        (uu___4457_32500.FStar_TypeChecker_Env.phase1);
                      FStar_TypeChecker_Env.failhard =
                        (uu___4457_32500.FStar_TypeChecker_Env.failhard);
                      FStar_TypeChecker_Env.nosynth =
                        (uu___4457_32500.FStar_TypeChecker_Env.nosynth);
                      FStar_TypeChecker_Env.uvar_subtyping =
                        (uu___4457_32500.FStar_TypeChecker_Env.uvar_subtyping);
                      FStar_TypeChecker_Env.tc_term =
                        (uu___4457_32500.FStar_TypeChecker_Env.tc_term);
                      FStar_TypeChecker_Env.type_of =
                        (uu___4457_32500.FStar_TypeChecker_Env.type_of);
                      FStar_TypeChecker_Env.universe_of =
                        (uu___4457_32500.FStar_TypeChecker_Env.universe_of);
                      FStar_TypeChecker_Env.check_type_of =
                        (uu___4457_32500.FStar_TypeChecker_Env.check_type_of);
                      FStar_TypeChecker_Env.use_bv_sorts =
                        (uu___4457_32500.FStar_TypeChecker_Env.use_bv_sorts);
                      FStar_TypeChecker_Env.qtbl_name_and_index =
                        (uu___4457_32500.FStar_TypeChecker_Env.qtbl_name_and_index);
                      FStar_TypeChecker_Env.normalized_eff_names =
                        (uu___4457_32500.FStar_TypeChecker_Env.normalized_eff_names);
                      FStar_TypeChecker_Env.fv_delta_depths =
                        (uu___4457_32500.FStar_TypeChecker_Env.fv_delta_depths);
                      FStar_TypeChecker_Env.proof_ns =
                        (uu___4457_32500.FStar_TypeChecker_Env.proof_ns);
                      FStar_TypeChecker_Env.synth_hook =
                        (uu___4457_32500.FStar_TypeChecker_Env.synth_hook);
                      FStar_TypeChecker_Env.try_solve_implicits_hook =
                        (uu___4457_32500.FStar_TypeChecker_Env.try_solve_implicits_hook);
                      FStar_TypeChecker_Env.splice =
                        (uu___4457_32500.FStar_TypeChecker_Env.splice);
                      FStar_TypeChecker_Env.mpreprocess =
                        (uu___4457_32500.FStar_TypeChecker_Env.mpreprocess);
                      FStar_TypeChecker_Env.postprocess =
                        (uu___4457_32500.FStar_TypeChecker_Env.postprocess);
                      FStar_TypeChecker_Env.is_native_tactic =
                        (uu___4457_32500.FStar_TypeChecker_Env.is_native_tactic);
                      FStar_TypeChecker_Env.identifier_info =
                        (uu___4457_32500.FStar_TypeChecker_Env.identifier_info);
                      FStar_TypeChecker_Env.tc_hooks =
                        (uu___4457_32500.FStar_TypeChecker_Env.tc_hooks);
                      FStar_TypeChecker_Env.dsenv =
                        (uu___4457_32500.FStar_TypeChecker_Env.dsenv);
                      FStar_TypeChecker_Env.nbe =
                        (uu___4457_32500.FStar_TypeChecker_Env.nbe);
                      FStar_TypeChecker_Env.strict_args_tab =
                        (uu___4457_32500.FStar_TypeChecker_Env.strict_args_tab);
                      FStar_TypeChecker_Env.erasable_types_tab =
                        (uu___4457_32500.FStar_TypeChecker_Env.erasable_types_tab);
                      FStar_TypeChecker_Env.enable_defer_to_tac = false
                    }  in
                  (env1.FStar_TypeChecker_Env.try_solve_implicits_hook env1
                     resolve_tac deferred_goals1;
                   guard))
          in
       let g1 = solve_deferred_constraints env g  in
       let g2 = solve_deferred_to_tactic g1  in
       (let uu____32506 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
            (FStar_Options.Other "ResolveImplicitsHook")
           in
        if uu____32506
        then
          let uu____32511 = guard_to_string env g2  in
          FStar_Util.print1
            "ResolveImplicitsHook: Solved deferred to tactic goals, remaining guard is\n%s\n"
            uu____32511
        else ());
       (let g3 = resolve_implicits env g2  in
        match g3.FStar_TypeChecker_Common.implicits with
        | [] ->
            let uu____32517 = discharge_guard env g3  in
            FStar_All.pipe_left (fun a2  -> ()) uu____32517
        | imp::uu____32519 ->
            let uu____32522 =
              let uu____32528 =
                let uu____32530 =
                  FStar_Syntax_Print.uvar_to_string
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_head
                   in
                let uu____32532 =
                  FStar_TypeChecker_Normalize.term_to_string env
                    (imp.FStar_TypeChecker_Common.imp_uvar).FStar_Syntax_Syntax.ctx_uvar_typ
                   in
                FStar_Util.format3
                  "Failed to resolve implicit argument %s of type %s introduced for %s"
                  uu____32530 uu____32532
                  imp.FStar_TypeChecker_Common.imp_reason
                 in
              (FStar_Errors.Fatal_FailToResolveImplicitArgument, uu____32528)
               in
            FStar_Errors.raise_error uu____32522
              imp.FStar_TypeChecker_Common.imp_range))
  
let (teq_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> unit)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32552 = teq env t1 t2  in
        force_trivial_guard env uu____32552
  
let (teq_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32571 = teq_nosmt env t1 t2  in
        match uu____32571 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  
let (universe_inequality :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.universe -> FStar_TypeChecker_Common.guard_t)
  =
  fun u1  ->
    fun u2  ->
      let uu___4482_32590 = FStar_TypeChecker_Common.trivial_guard  in
      {
        FStar_TypeChecker_Common.guard_f =
          (uu___4482_32590.FStar_TypeChecker_Common.guard_f);
        FStar_TypeChecker_Common.deferred_to_tac =
          (uu___4482_32590.FStar_TypeChecker_Common.deferred_to_tac);
        FStar_TypeChecker_Common.deferred =
          (uu___4482_32590.FStar_TypeChecker_Common.deferred);
        FStar_TypeChecker_Common.univ_ineqs = ([], [(u1, u2)]);
        FStar_TypeChecker_Common.implicits =
          (uu___4482_32590.FStar_TypeChecker_Common.implicits)
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
        (let uu____32626 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32626
         then
           let uu____32631 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32633 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "check_subtyping of %s and %s\n" uu____32631
             uu____32633
         else ());
        (let uu____32638 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32638 with
         | (prob,x,wl) ->
             let g =
               let uu____32657 =
                 solve_and_commit env (singleton wl prob true)
                   (fun uu____32668  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32657  in
             ((let uu____32690 =
                 (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                    (FStar_Options.Other "Rel"))
                   && (FStar_Util.is_some g)
                  in
               if uu____32690
               then
                 let uu____32695 =
                   FStar_TypeChecker_Normalize.term_to_string env t1  in
                 let uu____32697 =
                   FStar_TypeChecker_Normalize.term_to_string env t2  in
                 let uu____32699 =
                   let uu____32701 = FStar_Util.must g  in
                   guard_to_string env uu____32701  in
                 FStar_Util.print3
                   "check_subtyping succeeded: %s <: %s\n\tguard is %s\n"
                   uu____32695 uu____32697 uu____32699
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
        let uu____32738 = check_subtyping env t1 t2  in
        match uu____32738 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32757 =
              let uu____32758 = FStar_Syntax_Syntax.mk_binder x  in
              FStar_TypeChecker_Env.abstract_guard uu____32758 g  in
            FStar_Pervasives_Native.Some uu____32757
  
let (get_subtyping_prop :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32777 = check_subtyping env t1 t2  in
        match uu____32777 with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (x,g) ->
            let uu____32796 =
              let uu____32797 =
                let uu____32798 = FStar_Syntax_Syntax.mk_binder x  in
                [uu____32798]  in
              FStar_TypeChecker_Env.close_guard env uu____32797 g  in
            FStar_Pervasives_Native.Some uu____32796
  
let (subtype_nosmt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.typ ->
        FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        (let uu____32836 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Rel")
            in
         if uu____32836
         then
           let uu____32841 =
             FStar_TypeChecker_Normalize.term_to_string env t1  in
           let uu____32843 =
             FStar_TypeChecker_Normalize.term_to_string env t2  in
           FStar_Util.print2 "try_subtype_no_smt of %s and %s\n" uu____32841
             uu____32843
         else ());
        (let uu____32848 =
           new_t_prob (empty_worklist env) env t1
             FStar_TypeChecker_Common.SUB t2
            in
         match uu____32848 with
         | (prob,x,wl) ->
             let g =
               let uu____32863 =
                 solve_and_commit env (singleton wl prob false)
                   (fun uu____32874  -> FStar_Pervasives_Native.None)
                  in
               FStar_All.pipe_left (with_guard env prob) uu____32863  in
             (match g with
              | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
              | FStar_Pervasives_Native.Some g1 ->
                  let g2 =
                    let uu____32899 =
                      let uu____32900 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____32900]  in
                    FStar_TypeChecker_Env.close_guard env uu____32899 g1  in
                  discharge_guard' FStar_Pervasives_Native.None env g2 false))
  
let (subtype_nosmt_force :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ -> Prims.bool)
  =
  fun env  ->
    fun t1  ->
      fun t2  ->
        let uu____32941 = subtype_nosmt env t1 t2  in
        match uu____32941 with
        | FStar_Pervasives_Native.None  -> false
        | FStar_Pervasives_Native.Some g -> (force_trivial_guard env g; true)
  